/*
 * mac_udp.c — the untrusted UDP/QUIC IO shell for the proven datagram lane.
 *
 * The macOS/BSD sibling of ffi/mac_io.c, but for connectionless datagrams: it
 * owns a UDP socket, does `recvfrom`, hands the datagram bytes UNCHANGED to a
 * Lean callback (`ByteArray -> ByteArray`), and `sendto`s the callback's bytes
 * back to the sender. The callback is a pure `ByteArray -> ByteArray`; this file
 * never parses, decrypts, or rewrites a datagram — it only moves bytes across the
 * C<->Lean seam and logs sizes. Not verified; it is the environment the proven
 * core runs in.
 *
 * TWO CALLBACKS USE THIS SAME LOOP:
 *   * orb-mac-multi (IoMacMulti.udpHandle): treats the UDP payload as the
 *     already-decrypted application-data H3 stream (no packet protection) and
 *     drives the proven Reactor.QuicIngress.datagramServe.
 *   * orb-quic (IoQuic.quicDatagram): QUIC SOCKET-LIVE. The datagram is a QUIC
 *     long-header Initial packet; the Lean callback DECRYPTS it with the verified
 *     EverCrypt QUIC packet protection (QuicTransport.initialSecrets /
 *     deriveChachaKeys / openPacket) IN LEAN before it ever reaches datagramServe.
 *     This C shell still only shuttles bytes. What round-trips is a real UDP
 *     datagram whose protected payload is opened by verified crypto, then
 *     dispatched by the proven H3 ingress, over a real socket.
 *
 * SCOPE (honest, orb-quic): header protection (RFC 9001 §5.4) is not applied and
 * the Initial is ChaCha20-Poly1305 (not the AES-128-GCM a real client's Initial
 * uses); a full quiche/curl handshake needs both, plus the CRYPTO-frame /
 * ClientHello / 1-RTT key installation. See QUIC-SOCKET-README.md.
 */

#include <lean/lean.h>

#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>

/*
 * QUIC HEADER PROTECTION primitive (RFC 9001 §5.4.4) — the raw ChaCha20 block.
 *
 * QUIC header protection derives a 5-byte mask from a 16-byte ciphertext SAMPLE
 * by running the block cipher's keystream generator (RFC 9001 §5.4.3/§5.4.4).
 * For the ChaCha20-based suite that generator is the ChaCha20 block function with
 * counter = sample[0..4] (little-endian) and nonce = sample[4..16]. The verified
 * `Crypto` seam exposes only the ChaCha20-Poly1305 AEAD, not the bare keystream,
 * so this ONE extra crossing binds EverCrypt's verified ChaCha20 block
 * (`EverCrypt_Cipher_chacha20`, the portable HACL* Chacha20 the AEAD itself runs
 * on this arm64 host) so the mask can be computed with the SAME verified crypto.
 *
 * It is compiled into `orb-quic` (which already links libevercrypt.a); the
 * `#if __has_include` guard keeps `mac_udp.c` compilable by the plain
 * ffi/build-mac-multi.sh recipe (no EverCrypt include path) for the orb-mac-multi
 * lane, which never calls it. Assumed property (see QuicHeaderProt.lean): it is a
 * pure, deterministic function of (key, iv, ctr, src) — exactly what an XOR mask
 * needs. See QUIC-LIVE-README.md.
 *
 *   drorb_chacha20 : key(32) iv(12) (ctr : UInt32) src -> Option (keystream⊕src)
 */
#if __has_include("EverCrypt_Cipher.h")
#include "EverCrypt_Cipher.h"

#define DRORB_CC20_KEY   32u
#define DRORB_CC20_IV    12u

LEAN_EXPORT lean_object *drorb_chacha20(lean_object *key, lean_object *iv,
                                        uint32_t ctr, lean_object *src) {
    if (lean_sarray_size(key) != DRORB_CC20_KEY) return lean_box(0);
    if (lean_sarray_size(iv)  != DRORB_CC20_IV)  return lean_box(0);
    size_t n = lean_sarray_size(src);
    lean_object *out = lean_alloc_sarray(1, n, n);
    /* EverCrypt_Cipher_chacha20(len, dst, src, key, iv, ctr): dst = keystream⊕src.
     * With src = zeros, dst is the raw keystream — the header-protection mask. */
    EverCrypt_Cipher_chacha20((uint32_t)n, lean_sarray_cptr(out),
                              lean_sarray_cptr(src), lean_sarray_cptr(key),
                              lean_sarray_cptr(iv), ctr);
    lean_object *s = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(s, 0, out);
    return s;
}
#endif

/* Max datagram we will buffer (UDP payloads are bounded well under this). */
#define ORB_UDP_MAX 65536

static lean_object *udp_io_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/*
 * orb_mac_serve_udp : UInt16 -> (ByteArray -> ByteArray) -> IO Unit
 *
 * Bind 127.0.0.1:port as UDP, then loop forever: recvfrom one datagram, apply
 * the Lean handler to its bytes, sendto the handler's response bytes back to the
 * sender. Never returns under normal operation; returns an IO error only if the
 * socket cannot be brought up.
 */
LEAN_EXPORT lean_object *orb_mac_serve_udp(uint16_t port, lean_object *handler,
                                           lean_object *world) {
    (void)world;

    int usock = socket(AF_INET, SOCK_DGRAM, 0);
    if (usock < 0) return udp_io_err("orb-mac-multi/udp: socket() failed");

    int one = 1;
    setsockopt(usock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK); /* 127.0.0.1 */
    addr.sin_port = htons(port);

    if (bind(usock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(usock);
        return udp_io_err("orb-mac-multi/udp: bind() failed (port in use?)");
    }

    fprintf(stderr, "orb-mac-multi: QUIC/UDP listening on 127.0.0.1:%u (proven H3 datagram ingress over real UDP)\n",
            (unsigned)port);
    fflush(stderr);

    uint8_t buf[ORB_UDP_MAX];
    for (;;) {
        struct sockaddr_in src;
        socklen_t slen = sizeof(src);
        ssize_t n = recvfrom(usock, buf, sizeof(buf), 0,
                             (struct sockaddr *)&src, &slen);
        if (n < 0) { if (errno == EINTR) continue; break; }

        /* Wrap the datagram bytes as a Lean ByteArray. */
        lean_object *dg = lean_alloc_sarray(1, (size_t)n, (size_t)n);
        if (n) memcpy(lean_sarray_cptr(dg), buf, (size_t)n);

        /* The one seam crossing: the proven QUIC/H3 datagram path over these
         * bytes. lean_apply_1 consumes handler+dg, so inc the borrowed handler
         * first; it returns an owned ByteArray. */
        lean_inc(handler);
        lean_object *res = lean_apply_1(handler, dg);

        size_t rn = lean_sarray_size(res);
        fprintf(stderr,
                "orb-quic/udp: recv %zd bytes -> Lean callback -> %zu bytes %s\n",
                n, rn, rn ? "(decrypted+dispatched, sending response)"
                          : "(dropped: parse/AEAD-auth failure, no reply)");
        fflush(stderr);
        if (rn > 0)
            sendto(usock, lean_sarray_cptr(res), rn, 0,
                   (struct sockaddr *)&src, slen);
        lean_dec(res);
    }

    close(usock);
    return lean_io_result_mk_ok(lean_box(0));
}
