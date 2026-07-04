/*
 * mac_io.c — the untrusted IO shell for the proven reactor, macOS/BSD sockets.
 *
 * This C shim is NOT verified. It is the environment the proven core runs in:
 * it owns the socket, the accept loop, and the connection lifecycle, and it
 * does exactly one thing with the bytes — hand them, unchanged, to a Lean
 * callback (`ByteArray -> ByteArray`), then write the callback's bytes back and
 * close. The callback is the proven pipeline (`deployStepIngress`); this file
 * never inspects, parses, or rewrites a request or a response. Every crossing
 * of the C<->Lean seam is a plain `lean_apply_1`; there is no other coupling.
 *
 * v1 is a straight blocking accept loop — correctness over throughput. The
 * kqueue path (edge-triggered readiness, many live fds) is a drop-in
 * replacement for the loop body and is noted in MAC-IO-README.md; it changes
 * only how this shell schedules recv/accept, never what the core computes.
 */

#include <lean/lean.h>

#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <errno.h>
#include <ctype.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>

/* Cap on a single request head we will buffer before giving up (1 MiB). This is
 * an IO-shell resource bound, not a protocol decision; the core sees whatever
 * bytes we managed to read. */
#define ORB_MAX_REQ (1u << 20)

/* Scan buf[0..len) for the CRLFCRLF end-of-headers marker. Returns 1 if found.
 * We only serve request heads here (the curl GETs carry no body), so end of
 * headers is a complete-enough request for v1; a body-aware read would consult
 * Content-Length, which is the core's concern, not the shell's. */
static int has_headers_end(const uint8_t *buf, size_t len) {
    if (len < 4) return 0;
    for (size_t i = 0; i + 3 < len; i++) {
        if (buf[i] == '\r' && buf[i+1] == '\n' &&
            buf[i+2] == '\r' && buf[i+3] == '\n') return 1;
    }
    return 0;
}

/* Read one request from fd. Returns a freshly-allocated Lean ByteArray owning
 * the bytes read (possibly empty), or NULL on allocation failure. Reads until
 * CRLFCRLF, EOF, or the size cap. */
static lean_object *read_request(int fd) {
    size_t cap = 4096, len = 0;
    uint8_t *buf = (uint8_t *)malloc(cap);
    if (!buf) return NULL;

    for (;;) {
        if (len == cap) {
            if (cap >= ORB_MAX_REQ) break;
            size_t ncap = cap * 2;
            if (ncap > ORB_MAX_REQ) ncap = ORB_MAX_REQ;
            uint8_t *nb = (uint8_t *)realloc(buf, ncap);
            if (!nb) { free(buf); return NULL; }
            buf = nb; cap = ncap;
        }
        ssize_t n = recv(fd, buf + len, cap - len, 0);
        if (n < 0) { if (errno == EINTR) continue; break; }
        if (n == 0) break; /* peer closed */
        len += (size_t)n;
        if (has_headers_end(buf, len)) break;
    }

    lean_object *ba = lean_alloc_sarray(1, len, len);
    if (len) memcpy(lean_sarray_cptr(ba), buf, len);
    free(buf);
    return ba;
}

/* Write all n bytes of p to fd, retrying short/interrupted writes. */
static int write_all(int fd, const uint8_t *p, size_t n) {
    size_t off = 0;
    while (off < n) {
        ssize_t w = send(fd, p + off, n - off, 0);
        if (w < 0) { if (errno == EINTR) continue; return -1; }
        if (w == 0) return -1;
        off += (size_t)w;
    }
    return 0;
}

static lean_object *io_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/*
 * orb_mac_serve : UInt16 -> (ByteArray -> ByteArray) -> IO Unit
 *
 * Bind 127.0.0.1:port, then loop forever: accept, read the request bytes,
 * apply the Lean handler to them, write the handler's response bytes, close.
 * Never returns under normal operation; returns an IO error only if the socket
 * cannot be brought up.
 */
LEAN_EXPORT lean_object *orb_mac_serve(uint16_t port, lean_object *handler, lean_object *world) {
    (void)world;

    int lsock = socket(AF_INET, SOCK_STREAM, 0);
    if (lsock < 0) return io_err("orb-mac: socket() failed");

    int one = 1;
    setsockopt(lsock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK); /* 127.0.0.1 */
    addr.sin_port = htons(port);

    if (bind(lsock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(lsock);
        return io_err("orb-mac: bind() failed (port in use?)");
    }
    if (listen(lsock, 128) < 0) {
        close(lsock);
        return io_err("orb-mac: listen() failed");
    }

    fprintf(stderr, "orb-mac: listening on 127.0.0.1:%u (proven reactor over real TCP)\n",
            (unsigned)port);
    fflush(stderr);

    for (;;) {
        int cfd = accept(lsock, NULL, NULL);
        if (cfd < 0) { if (errno == EINTR) continue; break; }

        int nd = 1;
        setsockopt(cfd, IPPROTO_TCP, TCP_NODELAY, &nd, sizeof(nd));

        lean_object *req = read_request(cfd);
        if (req == NULL) { close(cfd); continue; }

        /* The one and only seam crossing: proven pipeline over these bytes.
         * lean_apply_1 consumes both the handler ref and req, so inc the
         * borrowed handler first; it returns an owned ByteArray. */
        lean_inc(handler);
        lean_object *res = lean_apply_1(handler, req);

        write_all(cfd, lean_sarray_cptr(res), lean_sarray_size(res));
        lean_dec(res);
        close(cfd);
    }

    close(lsock);
    return lean_io_result_mk_ok(lean_box(0));
}

/* ===================================================================== *
 * WebSocket lane (TASK MAC-MULTI): keep the TCP connection OPEN after an
 * RFC 6455 Upgrade and run every subsequent WS frame through the PROVEN
 * WebSocket path.
 *
 * The split is unchanged from the rest of this file: this C shell owns the
 * socket, the connection lifecycle, and — because the proven core ships no
 * SHA-1 (only SHA-256/384 in the EverCrypt shim) — the ONE handshake hash the
 * RFC requires for `Sec-WebSocket-Accept`. It never touches the WebSocket DATA
 * path: every frame's bytes are handed, unchanged, to the Lean `wsHandler`
 * (`orb_mac_ws_handle`), which decodes/unmasks/reassembles them with the REAL
 * `Reactor.Ws.wsFeedFn` and re-encodes the echo with the REAL
 * `Reactor.Ws.wsEncodeFn`. The shell writes those proven bytes back and loops.
 * ===================================================================== */

/* --- SHA-1 (RFC 3174), one-shot. Used ONLY for the handshake accept token;
 * it is never on the WebSocket data path. --- */
static void orb_sha1(const uint8_t *msg, size_t len, uint8_t out[20]) {
    uint32_t h0=0x67452301u,h1=0xEFCDAB89u,h2=0x98BADCFEu,h3=0x10325476u,h4=0xC3D2E1F0u;
    size_t ml = len + 1;
    while (ml % 64 != 56) ml++;
    size_t total = ml + 8;
    uint8_t *m = (uint8_t *)calloc(total, 1);
    if (!m) return;
    memcpy(m, msg, len);
    m[len] = 0x80;
    uint64_t bits = (uint64_t)len * 8;
    for (int i = 0; i < 8; i++) m[total - 1 - i] = (uint8_t)(bits >> (8 * i));
    for (size_t off = 0; off < total; off += 64) {
        uint32_t w[80];
        for (int i = 0; i < 16; i++)
            w[i] = ((uint32_t)m[off+4*i] << 24) | ((uint32_t)m[off+4*i+1] << 16)
                 | ((uint32_t)m[off+4*i+2] << 8) | (uint32_t)m[off+4*i+3];
        for (int i = 16; i < 80; i++) {
            uint32_t v = w[i-3] ^ w[i-8] ^ w[i-14] ^ w[i-16];
            w[i] = (v << 1) | (v >> 31);
        }
        uint32_t a=h0,b=h1,c=h2,d=h3,e=h4;
        for (int i = 0; i < 80; i++) {
            uint32_t f, k;
            if (i < 20)      { f = (b & c) | ((~b) & d);            k = 0x5A827999u; }
            else if (i < 40) { f = b ^ c ^ d;                      k = 0x6ED9EBA1u; }
            else if (i < 60) { f = (b & c) | (b & d) | (c & d);    k = 0x8F1BBCDCu; }
            else             { f = b ^ c ^ d;                      k = 0xCA62C1D6u; }
            uint32_t t = ((a << 5) | (a >> 27)) + f + e + k + w[i];
            e = d; d = c; c = (b << 30) | (b >> 2); b = a; a = t;
        }
        h0+=a; h1+=b; h2+=c; h3+=d; h4+=e;
    }
    free(m);
    uint32_t hs[5] = {h0,h1,h2,h3,h4};
    for (int i = 0; i < 5; i++) {
        out[4*i]   = (uint8_t)(hs[i] >> 24);
        out[4*i+1] = (uint8_t)(hs[i] >> 16);
        out[4*i+2] = (uint8_t)(hs[i] >> 8);
        out[4*i+3] = (uint8_t)(hs[i]);
    }
}

/* --- Base64 (RFC 4648) encode, used for the accept token. --- */
static void orb_b64(const uint8_t *in, size_t len, char *out) {
    static const char t[] =
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    size_t o = 0, i = 0;
    for (; i + 3 <= len; i += 3) {
        uint32_t v = ((uint32_t)in[i] << 16) | ((uint32_t)in[i+1] << 8) | in[i+2];
        out[o++] = t[(v>>18)&63]; out[o++] = t[(v>>12)&63];
        out[o++] = t[(v>>6)&63];  out[o++] = t[v&63];
    }
    if (len - i == 1) {
        uint32_t v = (uint32_t)in[i] << 16;
        out[o++] = t[(v>>18)&63]; out[o++] = t[(v>>12)&63];
        out[o++] = '='; out[o++] = '=';
    } else if (len - i == 2) {
        uint32_t v = ((uint32_t)in[i] << 16) | ((uint32_t)in[i+1] << 8);
        out[o++] = t[(v>>18)&63]; out[o++] = t[(v>>12)&63];
        out[o++] = t[(v>>6)&63];  out[o++] = '=';
    }
    out[o] = 0;
}

/* Case-insensitive substring search over a byte buffer; returns index or -1.
 * The shell uses this only to SELECT the WebSocket lane (analogous to the
 * proven Ingress fork on the h2 preface) and to lift the handshake key — never
 * to parse or rewrite the HTTP request the proven core answers. */
static long ci_find(const uint8_t *hay, size_t hlen, const char *needle) {
    size_t nl = strlen(needle);
    if (nl == 0 || nl > hlen) return -1;
    for (size_t i = 0; i + nl <= hlen; i++) {
        size_t j = 0;
        for (; j < nl; j++)
            if (tolower(hay[i+j]) != tolower((unsigned char)needle[j])) break;
        if (j == nl) return (long)i;
    }
    return -1;
}

/* Is this request an RFC 6455 WebSocket upgrade? (shell lane discriminator) */
static int is_ws_upgrade(const uint8_t *buf, size_t len) {
    return ci_find(buf, len, "sec-websocket-key:") >= 0
        && ci_find(buf, len, "websocket") >= 0;
}

/* Compute the Sec-WebSocket-Accept token from the request's Sec-WebSocket-Key.
 * accept = base64( sha1( key ++ "258EAFA5-E914-47DA-95CA-C5AB0DC85B11" ) ).
 * Writes a NUL-terminated token into out (>= 32 bytes). Returns 0 on success. */
static int ws_accept(const uint8_t *buf, size_t len, char *out) {
    long ki = ci_find(buf, len, "sec-websocket-key:");
    if (ki < 0) return -1;
    size_t p = (size_t)ki + strlen("sec-websocket-key:");
    while (p < len && (buf[p] == ' ' || buf[p] == '\t')) p++;
    size_t s = p;
    while (p < len && buf[p] != '\r' && buf[p] != '\n') p++;
    size_t klen = p - s;
    static const char GUID[] = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
    uint8_t cat[256];
    if (klen + sizeof(GUID) - 1 > sizeof(cat)) return -1;
    memcpy(cat, buf + s, klen);
    memcpy(cat + klen, GUID, sizeof(GUID) - 1);
    uint8_t dg[20];
    orb_sha1(cat, klen + sizeof(GUID) - 1, dg);
    orb_b64(dg, 20, out);
    return 0;
}

/* Read one chunk of WS frame bytes into a fresh Lean ByteArray (up to 64 KiB).
 * Returns NULL on EOF/error (caller closes). The proven wsFeedFn buffers a
 * partial frame in its own codec; this v1 shell feeds one recv per handler call
 * (small client frames arrive whole over loopback), which is a shell scheduling
 * choice, not a change to the proven decoder. */
static lean_object *read_ws_chunk(int fd) {
    uint8_t tmp[65536];
    ssize_t n;
    for (;;) {
        n = recv(fd, tmp, sizeof(tmp), 0);
        if (n < 0) { if (errno == EINTR) continue; return NULL; }
        break;
    }
    if (n == 0) return NULL; /* peer closed */
    lean_object *ba = lean_alloc_sarray(1, (size_t)n, (size_t)n);
    memcpy(lean_sarray_cptr(ba), tmp, (size_t)n);
    return ba;
}

/*
 * orb_mac_serve_ws
 *   : UInt16 -> (ByteArray -> ByteArray) -> (ByteArray -> ByteArray) -> IO Unit
 *
 * Bind 127.0.0.1:port and loop forever. For each connection, read the request
 * head:
 *   - If it is a WebSocket upgrade (RFC 6455), send the 101 handshake computed
 *     here (SHA-1 + Base64 of the client key), then KEEP THE CONNECTION OPEN and
 *     run a frame loop: every recv is handed to the Lean `wsHandler` (the proven
 *     wsFeedFn/wsEncodeFn echo), its bytes written straight back. The loop —
 *     hence one TCP connection — serves many frames until the peer closes.
 *   - Otherwise, answer once with the HTTP `handler` (the same proven
 *     deployStepIngress the plain orb-mac serves) and close.
 */
LEAN_EXPORT lean_object *orb_mac_serve_ws(uint16_t port, lean_object *handler,
                                          lean_object *wsHandler, lean_object *world) {
    (void)world;

    int lsock = socket(AF_INET, SOCK_STREAM, 0);
    if (lsock < 0) return io_err("orb-mac-multi/ws: socket() failed");

    int one = 1;
    setsockopt(lsock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = htons(port);

    if (bind(lsock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(lsock);
        return io_err("orb-mac-multi/ws: bind() failed (port in use?)");
    }
    if (listen(lsock, 128) < 0) {
        close(lsock);
        return io_err("orb-mac-multi/ws: listen() failed");
    }

    fprintf(stderr, "orb-mac-multi: WS+HTTP listening on 127.0.0.1:%u (proven WS frame path over real TCP)\n",
            (unsigned)port);
    fflush(stderr);

    for (;;) {
        int cfd = accept(lsock, NULL, NULL);
        if (cfd < 0) { if (errno == EINTR) continue; break; }

        int nd = 1;
        setsockopt(cfd, IPPROTO_TCP, TCP_NODELAY, &nd, sizeof(nd));

        lean_object *req = read_request(cfd);
        if (req == NULL) { close(cfd); continue; }

        const uint8_t *rp = lean_sarray_cptr(req);
        size_t rn = lean_sarray_size(req);

        if (is_ws_upgrade(rp, rn)) {
            char accept[64];
            if (ws_accept(rp, rn, accept) != 0) { lean_dec(req); close(cfd); continue; }
            lean_dec(req);

            char resp[256];
            int rlen = snprintf(resp, sizeof(resp),
                "HTTP/1.1 101 Switching Protocols\r\n"
                "Upgrade: websocket\r\n"
                "Connection: Upgrade\r\n"
                "Sec-WebSocket-Accept: %s\r\n\r\n", accept);
            if (rlen < 0 || write_all(cfd, (const uint8_t *)resp, (size_t)rlen) != 0) {
                close(cfd); continue;
            }
            fprintf(stderr, "orb-mac-multi: WS upgrade OK, accept=%s — connection open, frame loop\n", accept);
            fflush(stderr);

            /* KEEP-ALIVE WS FRAME LOOP over the one open connection. */
            for (;;) {
                lean_object *frame = read_ws_chunk(cfd);
                if (frame == NULL) break;             /* peer closed */
                lean_inc(wsHandler);
                lean_object *out = lean_apply_1(wsHandler, frame);  /* PROVEN wsFeedFn/wsEncodeFn */
                size_t on = lean_sarray_size(out);
                if (on > 0) {
                    if (write_all(cfd, lean_sarray_cptr(out), on) != 0) { lean_dec(out); break; }
                }
                lean_dec(out);
            }
            close(cfd);
        } else {
            /* Plain HTTP — the same proven handler orb-mac runs, one-shot. */
            lean_inc(handler);
            lean_object *res = lean_apply_1(handler, req);
            write_all(cfd, lean_sarray_cptr(res), lean_sarray_size(res));
            lean_dec(res);
            close(cfd);
        }
    }

    close(lsock);
    return lean_io_result_mk_ok(lean_box(0));
}
