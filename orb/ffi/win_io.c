/*
 * win_io.c — the untrusted IO shell for the proven reactor, Windows IOCP.
 *
 * This C shim is NOT verified. It is the environment the proven core runs in:
 * it owns the socket, the accept loop, and the connection lifecycle, and it
 * does exactly one thing with the bytes — hand them, unchanged, to a Lean
 * callback (`ByteArray -> ByteArray`), then write the callback's bytes back and
 * close. The callback is the proven pipeline (`deployStepIngress`); this file
 * never inspects, parses, or rewrites a request or a response. Every crossing
 * of the C<->Lean seam is a plain `lean_apply_1`; there is no other coupling.
 *
 * Backend: Windows I/O Completion Ports (IOCP), the native Windows proactor —
 * the counterpart to io_uring on Linux and kqueue on macOS/BSD. AcceptEx primes
 * accepts, WSARecv/WSASend carry the bytes, and a single GetQueuedCompletionStatus
 * loop drives every connection to completion. This is structurally the same
 * proactor shape as the io_uring backend in linux_io.c.
 *
 * SCOPE: this file cannot be built or run in the environment it was authored in
 * (macOS). The IOCP path is guarded by `#ifdef _WIN32` and only compiles under a
 * Windows toolchain (MSVC or clang-cl) linked against ws2_32/mswsock. On any
 * non-Windows host the exported symbol falls through to a stub that returns an IO
 * error, so IoWin.lean still typechecks, builds, and *links* everywhere (verified
 * on macOS). See WINDOWS-IO-README.md for what a real Windows build needs.
 *
 * The single Lean entry point is:
 *
 *     lean_object *orb_win_serve(uint16_t port,
 *                                lean_object *handler,   // ByteArray -> ByteArray
 *                                lean_object *world);     // IO token
 *
 * `handler` is a pure Lean closure. Each connection: build a ByteArray from the
 * request bytes, lean_inc(handler) (apply consumes its function), apply, take the
 * returned ByteArray's bytes, write them, dec the result.
 */

#include <lean/lean.h>

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ------------------------------------------------------------------------- */
/* Shared: end-of-headers detection (identical policy to the other shells).  */
/* For the proven H1/h2c core a GET/HEAD request head ends at CRLFCRLF and    */
/* carries no body, so that is our read-completion signal. Bodies are out of  */
/* scope for this shell; the core is fed the head verbatim, exactly as        */
/* Arena.Orb feeds a single stdin chunk.                                      */
/* ------------------------------------------------------------------------- */
static int orb_headers_done(const uint8_t *buf, size_t len) {
  if (len < 4) return 0;
  for (size_t i = 0; i + 3 < len; i++) {
    if (buf[i] == '\r' && buf[i+1] == '\n' &&
        buf[i+2] == '\r' && buf[i+3] == '\n')
      return 1;
  }
  return 0;
}

/* Cap a single request head at 1 MiB — the shell refuses anything larger. */
#define ORB_MAX_REQ (1u << 20)

/* Return a Lean IO error carrying `msg`. */
static lean_object *orb_io_err(const char *msg) {
  return lean_io_result_mk_error(
      lean_mk_io_user_error(lean_mk_string(msg)));
}

#ifdef _WIN32

/* ========================================================================= */
/* Windows IOCP proactor. Compile under MSVC/clang-cl; link ws2_32 + mswsock. */
/* ========================================================================= */

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <winsock2.h>
#include <ws2tcpip.h>
#include <mswsock.h>   /* AcceptEx, GetAcceptExSockaddrs, SO_UPDATE_ACCEPT_CONTEXT */

/* Kind of the async op an OVERLAPPED belongs to. The completion loop switches
 * on this to know what a dequeued packet means. */
typedef enum { ORB_OP_ACCEPT, ORB_OP_RECV, ORB_OP_SEND } orb_op_kind;

/* Per-operation context. `ov` MUST be first so a completed LPOVERLAPPED can be
 * cast straight back to an orb_ctx*. One is alive per outstanding accept and per
 * live connection. */
typedef struct {
  OVERLAPPED   ov;       /* the async handle IOCP hands back */
  orb_op_kind  kind;
  SOCKET       sock;     /* accept: the pre-created accept socket; else the conn */
  WSABUF       wsabuf;   /* current recv/send region into `buf` */
  uint8_t     *buf;      /* accumulation (recv) / response (send) buffer */
  size_t       len;      /* recv: bytes accumulated; send: total to send */
  size_t       cap;      /* capacity of `buf` */
  size_t       sent;     /* send: bytes already written */
  /* AcceptEx local+remote sockaddr landing zone (needs 2*(addr+16)). */
  uint8_t      acceptbuf[2 * (sizeof(struct sockaddr_in) + 16)];
} orb_ctx;

static orb_ctx *orb_ctx_new(size_t cap) {
  orb_ctx *c = (orb_ctx *)calloc(1, sizeof(orb_ctx));
  if (!c) return NULL;
  c->cap = cap;
  if (cap) {
    c->buf = (uint8_t *)malloc(cap);
    if (!c->buf) { free(c); return NULL; }
  }
  c->sock = INVALID_SOCKET;
  return c;
}

static void orb_ctx_free(orb_ctx *c) {
  if (!c) return;
  free(c->buf);
  free(c);
}

/* AcceptEx / GetAcceptExSockaddrs are Mswsock extension functions that must be
 * resolved at runtime through WSAIoctl(SIO_GET_EXTENSION_FUNCTION_POINTER). */
static LPFN_ACCEPTEX g_AcceptEx = NULL;

static int orb_load_acceptex(SOCKET lsock) {
  GUID guid = WSAID_ACCEPTEX;
  DWORD got = 0;
  if (WSAIoctl(lsock, SIO_GET_EXTENSION_FUNCTION_POINTER,
               &guid, sizeof(guid),
               &g_AcceptEx, sizeof(g_AcceptEx),
               &got, NULL, NULL) == SOCKET_ERROR)
    return -1;
  return 0;
}

/* Create a fresh accept socket and post an AcceptEx into a fresh accept ctx.
 * dwReceiveDataLength=0: AcceptEx only accepts, it does not wait for the first
 * byte, so a silent client cannot pin the accept. The first WSARecv follows on
 * completion. Returns the ctx (owned by the completion loop) or NULL. */
static orb_ctx *orb_post_accept(HANDLE iocp, SOCKET lsock) {
  SOCKET as = WSASocketW(AF_INET, SOCK_STREAM, IPPROTO_TCP,
                         NULL, 0, WSA_FLAG_OVERLAPPED);
  if (as == INVALID_SOCKET) return NULL;

  orb_ctx *c = orb_ctx_new(0);
  if (!c) { closesocket(as); return NULL; }
  c->kind = ORB_OP_ACCEPT;
  c->sock = as;

  DWORD recvd = 0;
  BOOL ok = g_AcceptEx(lsock, as, c->acceptbuf, 0,
                       sizeof(struct sockaddr_in) + 16,
                       sizeof(struct sockaddr_in) + 16,
                       &recvd, &c->ov);
  if (!ok && WSAGetLastError() != ERROR_IO_PENDING) {
    closesocket(as);
    orb_ctx_free(c);
    return NULL;
  }
  (void)iocp;
  return c;
}

/* Post a WSARecv into the tail of c->buf (growing if full). Returns 0 if the
 * recv is in flight, -1 on hard error (caller closes the connection). */
static int orb_post_recv(orb_ctx *c) {
  if (c->len == c->cap) {
    if (c->cap >= ORB_MAX_REQ) return -1;
    size_t ncap = c->cap ? c->cap * 2 : 8192;
    if (ncap > ORB_MAX_REQ) ncap = ORB_MAX_REQ;
    uint8_t *nb = (uint8_t *)realloc(c->buf, ncap);
    if (!nb) return -1;
    c->buf = nb; c->cap = ncap;
  }
  memset(&c->ov, 0, sizeof(c->ov));
  c->kind = ORB_OP_RECV;
  c->wsabuf.buf = (CHAR *)(c->buf + c->len);
  c->wsabuf.len = (ULONG)(c->cap - c->len);
  DWORD flags = 0, got = 0;
  int r = WSARecv(c->sock, &c->wsabuf, 1, &got, &flags, &c->ov, NULL);
  if (r == SOCKET_ERROR && WSAGetLastError() != WSA_IO_PENDING) return -1;
  return 0;
}

/* Post a WSASend of the not-yet-sent tail of the response. Returns 0 in flight,
 * -1 on hard error. */
static int orb_post_send(orb_ctx *c) {
  memset(&c->ov, 0, sizeof(c->ov));
  c->kind = ORB_OP_SEND;
  c->wsabuf.buf = (CHAR *)(c->buf + c->sent);
  c->wsabuf.len = (ULONG)(c->len - c->sent);
  DWORD got = 0;
  int r = WSASend(c->sock, &c->wsabuf, 1, &got, 0, &c->ov, NULL);
  if (r == SOCKET_ERROR && WSAGetLastError() != WSA_IO_PENDING) return -1;
  return 0;
}

/*
 * The one and only seam crossing. When the request head is complete, replace the
 * accumulation buffer's contents with the proven core's response: build a Lean
 * ByteArray from (c->buf, c->len), apply the borrowed handler (lean_inc first,
 * since lean_apply_1 consumes the closure), copy the returned bytes back into a
 * send buffer on the ctx, and set up for WSASend. `handler` is never mutated;
 * this file computes nothing about the bytes.
 */
static int orb_run_core(orb_ctx *c, lean_object *handler) {
  lean_object *req = lean_alloc_sarray(1, c->len, c->len);
  if (c->len) memcpy(lean_sarray_cptr(req), c->buf, c->len);

  lean_inc(handler);
  lean_object *resp = lean_apply_1(handler, req); /* consumes req + inc'd handler */

  size_t rlen = lean_sarray_size(resp);
  const uint8_t *rptr = lean_sarray_cptr(resp);

  /* Reuse or resize the ctx buffer to hold the response for the send phase. */
  if (rlen > c->cap) {
    uint8_t *nb = (uint8_t *)realloc(c->buf, rlen);
    if (!nb) { lean_dec(resp); return -1; }
    c->buf = nb; c->cap = rlen;
  }
  if (rlen) memcpy(c->buf, rptr, rlen);
  c->len = rlen;
  c->sent = 0;
  lean_dec(resp);
  return orb_post_send(c);
}

static void orb_close(orb_ctx *c) {
  if (c->sock != INVALID_SOCKET) closesocket(c->sock);
  orb_ctx_free(c);
}

/* Bind + listen an overlapped listen socket on 0.0.0.0:port. */
static SOCKET orb_make_listener(uint16_t port) {
  SOCKET lsock = WSASocketW(AF_INET, SOCK_STREAM, IPPROTO_TCP,
                            NULL, 0, WSA_FLAG_OVERLAPPED);
  if (lsock == INVALID_SOCKET) return INVALID_SOCKET;

  BOOL one = TRUE;
  setsockopt(lsock, SOL_SOCKET, SO_REUSEADDR, (const char *)&one, sizeof(one));

  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_ANY);
  addr.sin_port = htons(port);

  if (bind(lsock, (struct sockaddr *)&addr, sizeof(addr)) == SOCKET_ERROR) {
    closesocket(lsock);
    return INVALID_SOCKET;
  }
  if (listen(lsock, SOMAXCONN) == SOCKET_ERROR) {
    closesocket(lsock);
    return INVALID_SOCKET;
  }
  return lsock;
}

/*
 * orb_win_serve : UInt16 -> (ByteArray -> ByteArray) -> IO Unit
 *
 * Bring up Winsock + an IOCP, bind 0.0.0.0:port, prime a batch of AcceptEx, and
 * run one GetQueuedCompletionStatus loop that drives every connection —
 * accept -> recv (until CRLFCRLF / EOF / cap) -> run the proven core -> send ->
 * close. Never returns under normal operation; returns an IO error only if the
 * socket stack cannot be brought up.
 */
LEAN_EXPORT lean_object *orb_win_serve(uint16_t port, lean_object *handler,
                                       lean_object *world) {
  (void)world;

  WSADATA wsa;
  if (WSAStartup(MAKEWORD(2, 2), &wsa) != 0) {
    lean_dec(handler);
    return orb_io_err("orb-win: WSAStartup failed");
  }

  SOCKET lsock = orb_make_listener(port);
  if (lsock == INVALID_SOCKET) {
    WSACleanup();
    lean_dec(handler);
    return orb_io_err("orb-win: bind/listen failed (port in use?)");
  }

  HANDLE iocp = CreateIoCompletionPort(INVALID_HANDLE_VALUE, NULL, 0, 0);
  if (!iocp) {
    closesocket(lsock);
    WSACleanup();
    lean_dec(handler);
    return orb_io_err("orb-win: CreateIoCompletionPort failed");
  }
  if (!CreateIoCompletionPort((HANDLE)lsock, iocp, 0, 0)) {
    CloseHandle(iocp);
    closesocket(lsock);
    WSACleanup();
    lean_dec(handler);
    return orb_io_err("orb-win: associate listener with IOCP failed");
  }
  if (orb_load_acceptex(lsock) != 0) {
    CloseHandle(iocp);
    closesocket(lsock);
    WSACleanup();
    lean_dec(handler);
    return orb_io_err("orb-win: could not resolve AcceptEx");
  }

  /* Keep a small pool of outstanding accepts so bursts are not serialized. */
  const int ORB_ACCEPT_BACKLOG = 16;
  for (int i = 0; i < ORB_ACCEPT_BACKLOG; i++) {
    (void)orb_post_accept(iocp, lsock);
  }

  fprintf(stderr, "orb-win: IOCP serving on 0.0.0.0:%u (proven reactor over real TCP)\n",
          (unsigned)port);
  fflush(stderr);

  for (;;) {
    DWORD bytes = 0;
    ULONG_PTR key = 0;
    LPOVERLAPPED ov = NULL;
    BOOL ok = GetQueuedCompletionStatus(iocp, &bytes, &key, &ov, INFINITE);

    if (!ov) {
      /* No completion packet (e.g. IOCP torn down) — nothing to reclaim. */
      if (!ok) break;
      continue;
    }

    orb_ctx *c = (orb_ctx *)ov; /* ov is the first field of orb_ctx */

    if (!ok) {
      /* The op failed (peer reset, cancel). Reclaim the connection; if this was
       * an accept, re-prime one so the backlog does not drain. */
      orb_op_kind k = c->kind;
      orb_close(c);
      if (k == ORB_OP_ACCEPT) (void)orb_post_accept(iocp, lsock);
      continue;
    }

    switch (c->kind) {
      case ORB_OP_ACCEPT: {
        /* Inherit the listener's properties, then bind the new socket to IOCP. */
        setsockopt(c->sock, SOL_SOCKET, SO_UPDATE_ACCEPT_CONTEXT,
                   (const char *)&lsock, sizeof(lsock));
        if (!CreateIoCompletionPort((HANDLE)c->sock, iocp, 0, 0)) {
          orb_close(c);
          (void)orb_post_accept(iocp, lsock);
          break;
        }
        /* Re-prime an accept to keep the backlog full, then start reading. */
        (void)orb_post_accept(iocp, lsock);
        c->len = 0;
        if (orb_post_recv(c) != 0) orb_close(c);
        break;
      }

      case ORB_OP_RECV: {
        if (bytes == 0) {
          /* peer closed: process whatever head we have. */
          if (orb_run_core(c, handler) != 0) orb_close(c);
          break;
        }
        c->len += (size_t)bytes;
        if (orb_headers_done(c->buf, c->len) || c->len >= ORB_MAX_REQ) {
          if (orb_run_core(c, handler) != 0) orb_close(c);
        } else {
          if (orb_post_recv(c) != 0) orb_close(c);
        }
        break;
      }

      case ORB_OP_SEND: {
        c->sent += (size_t)bytes;
        if (c->sent < c->len) {
          if (orb_post_send(c) != 0) orb_close(c);
        } else {
          /* v1: one response per connection, then close (no keep-alive). */
          orb_close(c);
        }
        break;
      }
    }
  }

  CloseHandle(iocp);
  closesocket(lsock);
  WSACleanup();
  lean_dec(handler);
  return lean_io_result_mk_ok(lean_box(0));
}

#else /* !_WIN32 */

/* ========================================================================= */
/* Non-Windows stub: keeps the Lean @[extern] decl linkable on macOS/Linux.  */
/* Compiling win_io.c on a non-Windows host yields exactly this symbol, so    */
/* IoWin.lean typechecks and the `orb-win` exe links (against the stub) here. */
/* ========================================================================= */

LEAN_EXPORT lean_object *orb_win_serve(uint16_t port, lean_object *handler,
                                       lean_object *world) {
  (void)port;
  (void)world;
  lean_dec(handler);
  return orb_io_err("orb_win_serve: this driver is Windows-only (IOCP); "
                    "build and run it on Windows with MSVC + ws2_32");
}

#endif /* _WIN32 */
