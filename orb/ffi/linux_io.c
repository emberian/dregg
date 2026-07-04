/*
 * linux_io.c — the untrusted IO shell for the proven reactor.
 *
 * This file owns NOTHING about request semantics. It is a socket accept loop:
 * it accepts a connection, reads the request bytes into a buffer, hands that
 * buffer to the PROVEN Lean core (`Reactor.Ingress.deployStepIngress`, wrapped
 * as a `ByteArray -> ByteArray` closure by IoLinux.lean), and writes the bytes
 * the core returns straight back to the socket. The processing is the proven
 * Lean; everything in this file is the tested-not-proven environment.
 *
 * Two Linux backends, selected at compile time:
 *   - default: epoll(7) level-triggered readiness loop, no external deps.
 *   - ORB_IO_URING: io_uring(7) proactor via liburing (-luring).
 * On a non-Linux host the exported symbol is a stub that returns an IO error,
 * so the Lean side still typechecks, builds, and links (verified on macOS).
 *
 * The single Lean entry point is:
 *
 *     lean_object *orb_linux_serve(uint16_t port,
 *                                  lean_object *handler,   // ByteArray -> ByteArray
 *                                  lean_object *world);    // IO token
 *
 * `handler` is a pure Lean closure. Each connection: build a ByteArray from the
 * request bytes, lean_inc(handler) (apply consumes its function), apply, take
 * the returned ByteArray's bytes, write them, dec the result.
 */

#include <lean/lean.h>

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ------------------------------------------------------------------------- */
/* Shared: run one request buffer through the proven Lean core.              */
/* ------------------------------------------------------------------------- */

#ifdef __linux__

#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <arpa/inet.h>

/* Cap a single request head at 1 MiB — the shell refuses anything larger. */
#define ORB_MAX_REQ (1u << 20)

/* Write all `len` bytes of `buf` to a (blocking) fd; returns 0 on success. */
static int orb_write_all(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = write(fd, buf + off, len - off);
    if (n < 0) {
      if (errno == EINTR) continue;
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

/*
 * The proven step, applied to one request buffer. Builds a Lean ByteArray from
 * (buf, len), applies `handler` (the deployStepIngress wrapper), and writes the
 * response bytes to `fd`. `handler` is borrowed: we lean_inc before applying
 * because lean_apply_1 consumes the closure.
 */
static void orb_process(int fd, lean_object *handler,
                        const uint8_t *buf, size_t len) {
  lean_object *req = lean_alloc_sarray(1, len, len);
  if (len) memcpy(lean_sarray_cptr(req), buf, len);

  lean_inc(handler);
  lean_object *resp = lean_apply_1(handler, req); /* consumes req + inc'd handler */

  size_t rlen = lean_sarray_size(resp);
  const uint8_t *rptr = lean_sarray_cptr(resp);
  (void)orb_write_all(fd, rptr, rlen);

  lean_dec(resp);
}

static int orb_set_nonblocking(int fd) {
  int fl = fcntl(fd, F_GETFL, 0);
  if (fl < 0) return -1;
  return fcntl(fd, F_SETFL, fl | O_NONBLOCK);
}

static int orb_set_blocking(int fd) {
  int fl = fcntl(fd, F_GETFL, 0);
  if (fl < 0) return -1;
  return fcntl(fd, F_SETFL, fl & ~O_NONBLOCK);
}

/* Bind + listen on 0.0.0.0:port. Returns the listener fd, or -1. */
static int orb_make_listener(uint16_t port) {
  int lfd = socket(AF_INET, SOCK_STREAM, 0);
  if (lfd < 0) return -1;

  int one = 1;
  setsockopt(lfd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_ANY);
  addr.sin_port = htons(port);

  if (bind(lfd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    close(lfd);
    return -1;
  }
  if (listen(lfd, 128) < 0) {
    close(lfd);
    return -1;
  }
  return lfd;
}

/* Return a Lean IO error carrying `msg`. */
static lean_object *orb_io_err(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/*
 * Detect end-of-headers. For the proven H1/h2c core, a GET/HEAD request head
 * ends at CRLFCRLF and carries no body, so that is our read-completion signal.
 * (Bodies are out of scope for this shell; the core is fed the head verbatim,
 * exactly as Arena.Orb feeds a single stdin chunk.) Returns 1 if `buf` of
 * length `len` contains "\r\n\r\n".
 */
static int orb_headers_done(const uint8_t *buf, size_t len) {
  if (len < 4) return 0;
  for (size_t i = 0; i + 3 < len; i++) {
    if (buf[i] == '\r' && buf[i+1] == '\n' &&
        buf[i+2] == '\r' && buf[i+3] == '\n')
      return 1;
  }
  return 0;
}

/* ========================================================================= */
/* Backend A: io_uring (liburing).  Compile with -DORB_IO_URING -luring.     */
/* ========================================================================= */
#ifdef ORB_IO_URING
#include <liburing.h>

/* Per-connection read buffer for the io_uring proactor. */
typedef struct {
  int      fd;
  uint8_t *buf;
  size_t   len;
  size_t   cap;
} orb_conn;

static orb_conn *orb_conn_new(int fd) {
  orb_conn *c = (orb_conn *)calloc(1, sizeof(orb_conn));
  if (!c) return NULL;
  c->fd = fd;
  c->cap = 8192;
  c->buf = (uint8_t *)malloc(c->cap);
  if (!c->buf) { free(c); return NULL; }
  return c;
}

static void orb_conn_free(orb_conn *c) {
  if (!c) return;
  free(c->buf);
  free(c);
}

/* Marker tags packed into user_data via the low bit. */
#define ORB_TAG_ACCEPT ((void *)0x1)

lean_object *orb_linux_serve(uint16_t port, lean_object *handler,
                             lean_object *world) {
  (void)world;
  signal(SIGPIPE, SIG_IGN);

  int lfd = orb_make_listener(port);
  if (lfd < 0) { lean_dec(handler); return orb_io_err("orb: bind/listen failed"); }

  struct io_uring ring;
  if (io_uring_queue_init(256, &ring, 0) < 0) {
    close(lfd);
    lean_dec(handler);
    return orb_io_err("orb: io_uring_queue_init failed");
  }

  struct sockaddr_in caddr;
  socklen_t clen = sizeof(caddr);

  /* Prime an accept. */
  struct io_uring_sqe *sqe = io_uring_get_sqe(&ring);
  io_uring_prep_accept(sqe, lfd, (struct sockaddr *)&caddr, &clen, 0);
  io_uring_sqe_set_data(sqe, ORB_TAG_ACCEPT);
  io_uring_submit(&ring);

  fprintf(stderr, "orb-linux: io_uring serving on 0.0.0.0:%u\n", (unsigned)port);

  for (;;) {
    struct io_uring_cqe *cqe;
    if (io_uring_wait_cqe(&ring, &cqe) < 0) break;

    void *data = io_uring_cqe_get_data(cqe);
    int res = cqe->res;

    if (data == ORB_TAG_ACCEPT) {
      /* Re-arm accept immediately. */
      struct io_uring_sqe *asqe = io_uring_get_sqe(&ring);
      io_uring_prep_accept(asqe, lfd, (struct sockaddr *)&caddr, &clen, 0);
      io_uring_sqe_set_data(asqe, ORB_TAG_ACCEPT);
      io_uring_submit(&ring);

      if (res >= 0) {
        orb_conn *c = orb_conn_new(res);
        if (c) {
          struct io_uring_sqe *rsqe = io_uring_get_sqe(&ring);
          io_uring_prep_recv(rsqe, c->fd, c->buf, c->cap, 0);
          io_uring_sqe_set_data(rsqe, c);
          io_uring_submit(&ring);
        } else {
          close(res);
        }
      }
    } else if (data != NULL) {
      orb_conn *c = (orb_conn *)data;
      if (res <= 0) {
        close(c->fd);
        orb_conn_free(c);
      } else {
        c->len += (size_t)res; /* recv wrote into buf at offset 0 each time; */
        /* single-shot read is sufficient for header-only requests. */
        if (orb_headers_done(c->buf, c->len) || c->len >= ORB_MAX_REQ) {
          orb_set_blocking(c->fd);
          orb_process(c->fd, handler, c->buf, c->len);
          close(c->fd);
          orb_conn_free(c);
        } else {
          /* Need more: grow if full and re-arm recv into the tail. */
          if (c->len == c->cap) {
            size_t ncap = c->cap * 2;
            uint8_t *nb = (uint8_t *)realloc(c->buf, ncap);
            if (!nb) { close(c->fd); orb_conn_free(c); io_uring_cqe_seen(&ring, cqe); continue; }
            c->buf = nb; c->cap = ncap;
          }
          struct io_uring_sqe *rsqe = io_uring_get_sqe(&ring);
          io_uring_prep_recv(rsqe, c->fd, c->buf + c->len, c->cap - c->len, 0);
          io_uring_sqe_set_data(rsqe, c);
          io_uring_submit(&ring);
        }
      }
    }
    io_uring_cqe_seen(&ring, cqe);
  }

  io_uring_queue_exit(&ring);
  close(lfd);
  lean_dec(handler);
  return lean_io_result_mk_ok(lean_box(0));
}

/* ========================================================================= */
/* Backend B: epoll (default). Level-triggered readiness, no external deps.  */
/* ========================================================================= */
#else /* !ORB_IO_URING */
#include <sys/epoll.h>

#define ORB_MAX_FDS 65536

typedef struct {
  uint8_t *buf;
  size_t   len;
  size_t   cap;
  int      active;
} orb_slot;

static orb_slot g_conns[ORB_MAX_FDS];

static void orb_slot_reset(int fd) {
  if (fd < 0 || fd >= ORB_MAX_FDS) return;
  free(g_conns[fd].buf);
  g_conns[fd].buf = NULL;
  g_conns[fd].len = 0;
  g_conns[fd].cap = 0;
  g_conns[fd].active = 0;
}

static void orb_close_conn(int epfd, int fd) {
  epoll_ctl(epfd, EPOLL_CTL_DEL, fd, NULL);
  close(fd);
  orb_slot_reset(fd);
}

lean_object *orb_linux_serve(uint16_t port, lean_object *handler,
                             lean_object *world) {
  (void)world;
  signal(SIGPIPE, SIG_IGN);

  int lfd = orb_make_listener(port);
  if (lfd < 0) { lean_dec(handler); return orb_io_err("orb: bind/listen failed"); }
  orb_set_nonblocking(lfd);

  int epfd = epoll_create1(0);
  if (epfd < 0) { close(lfd); lean_dec(handler); return orb_io_err("orb: epoll_create1 failed"); }

  struct epoll_event ev;
  memset(&ev, 0, sizeof(ev));
  ev.events = EPOLLIN;
  ev.data.fd = lfd;
  epoll_ctl(epfd, EPOLL_CTL_ADD, lfd, &ev);

  fprintf(stderr, "orb-linux: epoll serving on 0.0.0.0:%u\n", (unsigned)port);

  struct epoll_event events[64];
  for (;;) {
    int n = epoll_wait(epfd, events, 64, -1);
    if (n < 0) { if (errno == EINTR) continue; break; }

    for (int i = 0; i < n; i++) {
      int fd = events[i].data.fd;

      if (fd == lfd) {
        /* Drain the accept backlog. */
        for (;;) {
          int cfd = accept(lfd, NULL, NULL);
          if (cfd < 0) {
            if (errno == EAGAIN || errno == EWOULDBLOCK) break;
            if (errno == EINTR) continue;
            break;
          }
          if (cfd >= ORB_MAX_FDS) { close(cfd); continue; }
          orb_set_nonblocking(cfd);
          g_conns[cfd].active = 1;
          g_conns[cfd].len = 0;
          g_conns[cfd].cap = 8192;
          g_conns[cfd].buf = (uint8_t *)malloc(g_conns[cfd].cap);
          if (!g_conns[cfd].buf) { close(cfd); orb_slot_reset(cfd); continue; }
          struct epoll_event cev;
          memset(&cev, 0, sizeof(cev));
          cev.events = EPOLLIN;
          cev.data.fd = cfd;
          epoll_ctl(epfd, EPOLL_CTL_ADD, cfd, &cev);
        }
        continue;
      }

      /* A client fd is readable. */
      orb_slot *c = &g_conns[fd];
      if (!c->active) { orb_close_conn(epfd, fd); continue; }

      int done = 0, dead = 0;
      for (;;) {
        if (c->len == c->cap) {
          if (c->cap >= ORB_MAX_REQ) { done = 1; break; }
          size_t ncap = c->cap * 2;
          uint8_t *nb = (uint8_t *)realloc(c->buf, ncap);
          if (!nb) { dead = 1; break; }
          c->buf = nb; c->cap = ncap;
        }
        ssize_t r = read(fd, c->buf + c->len, c->cap - c->len);
        if (r > 0) {
          c->len += (size_t)r;
          if (orb_headers_done(c->buf, c->len)) { done = 1; break; }
          continue;
        } else if (r == 0) {
          /* peer closed; process whatever we have */
          done = 1; break;
        } else {
          if (errno == EAGAIN || errno == EWOULDBLOCK) break; /* wait for more */
          if (errno == EINTR) continue;
          dead = 1; break;
        }
      }

      if (dead) { orb_close_conn(epfd, fd); continue; }
      if (done) {
        orb_set_blocking(fd);
        orb_process(fd, handler, c->buf, c->len);
        orb_close_conn(epfd, fd);
      }
    }
  }

  close(epfd);
  close(lfd);
  lean_dec(handler);
  return lean_io_result_mk_ok(lean_box(0));
}

#endif /* ORB_IO_URING */

/* ========================================================================= */
/* Non-Linux stub: keeps the Lean @[extern] decl linkable on macOS et al.    */
/* ========================================================================= */
#else /* !__linux__ */

lean_object *orb_linux_serve(uint16_t port, lean_object *handler,
                             lean_object *world) {
  (void)port;
  (void)world;
  lean_dec(handler);
  return lean_io_result_mk_error(
      lean_mk_io_user_error(
          lean_mk_string("orb_linux_serve: this driver is Linux-only "
                         "(io_uring/epoll); build and run it on Linux")));
}

#endif /* __linux__ */
