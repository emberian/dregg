/* lean_init.c — a tiny C shim performing the Lean C-embedding init ritual.
 *
 * Many of the runtime entry points the ritual needs (`lean_io_mk_world`,
 * `lean_io_result_is_ok`, `lean_dec_ref`) are `static inline` in <lean/lean.h>
 * and therefore have NO linkable symbol — they can only be used from C that
 * includes the header. So we wrap the whole ritual here and expose a single
 * plain exported function for Rust to call.
 */
#include <stdint.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);

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
