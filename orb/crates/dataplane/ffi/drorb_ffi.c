/*
 * drorb_ffi.c — the byte-marshalling adapter between the Rust dataplane and the
 * leanc-compiled proven serve.
 *
 * The Lean ByteArray ABI (an `sarray` object) is reached through accessors that
 * <lean/lean.h> defines as `static inline` — so they are not linkable symbols a
 * foreign caller can name. This shim includes lean.h and re-exposes exactly the
 * handful the host needs as plain C entry points. It parses nothing and holds no
 * state; it moves bytes across the sarray boundary and nothing else. The runtime
 * init and the `drorb_serve` call itself are made by the Rust host directly
 * against the real exported symbols.
 */
#include <lean/lean.h>
#include <string.h>
#include <stdint.h>

/* Wrap `n` host bytes in a fresh Lean ByteArray (sarray). The returned object is
 * owned; `drorb_serve` consumes it. */
lean_object *drorb_sarray_of_bytes(const uint8_t *p, size_t n) {
    lean_object *o = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(o), p, n);
    return o;
}

/* Length and data pointer of a Lean ByteArray (the response sarray). */
size_t drorb_sarray_len(lean_object *o) { return lean_sarray_size(o); }
const uint8_t *drorb_sarray_ptr(lean_object *o) { return lean_sarray_cptr(o); }

/* Drop an owned Lean object reference. */
void drorb_obj_dec(lean_object *o) { lean_dec(o); }

/* The RealWorld token threaded through Lean IO / module initializers. */
lean_object *drorb_io_world(void) { return lean_io_mk_world(); }

/* Did a Lean `IO α` result come back ok (vs. an error)? */
int drorb_io_ok(lean_object *o) { return lean_io_result_is_ok(o) ? 1 : 0; }
