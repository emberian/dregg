/* lean_init.c — a tiny C shim performing the Lean C-embedding init ritual.
 *
 * Many of the runtime entry points the ritual needs (`lean_io_mk_world`,
 * `lean_io_result_is_ok`, `lean_dec_ref`) are `static inline` in <lean/lean.h>
 * and therefore have NO linkable symbol — they can only be used from C that
 * includes the header. So we wrap the whole ritual here and expose a single
 * plain exported function for Rust to call.
 */
#include <stdint.h>
#include <string.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);

/* The @[export]ed Lean `String -> String` state-marshalling step. At the C ABI a Lean
 * `String` is a `lean_object*`, so this takes/returns boxed Lean strings — which is why
 * it must be driven from C (the `lean_mk_string`/`lean_string_cstr` helpers below). */
extern lean_object *dregg_record_kernel_step(lean_object *input);

/* The @[export]ed Lean `String -> String` CAPS-bearing step: same shape, but the wire also
 * carries the held-cap table so the cross-vat / held-cap branch of `authorizedB` is exercised. */
extern lean_object *dregg_record_kernel_step_caps(lean_object *input);

/* The @[export]ed Lean `String -> String` FULL-TURN executor: decodes a
 * (RecChainedState, List FullAction), runs the PROVED `execFullTurn` (all-or-nothing), and
 * re-encodes the resulting Option state (post-cells + post-caps + receipt-log length + commit). */
extern lean_object *dregg_exec_full_turn(lean_object *input);

/* Returns 0 on success, 1 if module initialization reported an IO error. */
int dregg_ffi_init(void) {
    lean_initialize_runtime_module();
    lean_object *res = initialize_Dregg2_Dregg2_Exec_FFI(1);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();
    return 0;
}

/* dregg_record_kernel_step_str — a plain-C string bridge over the Lean `String -> String`
 * record-cell-state step export.
 *
 * `in_utf8` is a NUL-terminated UTF-8 wire string (the JSON `RecordKernelState` + turn).
 * We box it into a Lean string, call the verified `dregg_record_kernel_step`, copy the
 * result into the caller-owned `out` buffer (NUL-terminated, truncated to `out_cap-1`),
 * and decref the Lean objects.
 *
 * Returns the FULL byte length of the result string (excluding the NUL). If that is
 * >= out_cap the output was truncated and the caller should retry with a larger buffer.
 * Returns (size_t)-1 only if `out`/`out_cap` are unusable. */
size_t dregg_record_kernel_step_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);   /* takes ownership semantics: refcount 1 */
    lean_object *res = dregg_record_kernel_step(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_record_kernel_step_caps_str — the caps-bearing analog of the bridge above. Identical
 * marshalling discipline; the only difference is it drives `dregg_record_kernel_step_caps`,
 * whose input wire also carries the `Caps` table. Same return contract (full byte length;
 * (size_t)-1 only on an unusable buffer). */
size_t dregg_record_kernel_step_caps_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_record_kernel_step_caps(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_exec_full_turn_str — the C string bridge over the Lean `String -> String` FULL-TURN
 * executor export. Identical marshalling discipline as the step bridges above; it drives
 * `dregg_exec_full_turn`, whose input wire is `{"cells":CELLS,"caps":CAPS,"actions":ACTIONS}`
 * and whose output is `{"cells":CELLS,"caps":CAPS,"loglen":N,"ok":B}`. Same return contract
 * (full byte length; (size_t)-1 only on an unusable buffer). */
size_t dregg_exec_full_turn_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_exec_full_turn(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
