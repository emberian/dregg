/* driver.c — the C seam between the commit PD (src/main.rs) and the Lean step function.
 *
 *   chokepoint_init()            Lean runtime + module init for CommitBytes (and its imports
 *                                Init, Compiler.Blake3, CommitStep). Returns 0 on success.
 *   chokepoint_arrive(w, n, o, c) one call of `dregg_chokepoint_arrive : String -> String`
 *                                (CommitBytes.lean). Copies the reply into o[0..c) with a NUL;
 *                                returns its length, or -1 if it does not fit.
 *
 * The decision and the leaf bytes are computed by the Lean definition the theorems are about;
 * this file only moves bytes. Init for COMPILED Lean (no lean_initialize, which would pull the
 * elaborator), the same contract as ../../executor-microkit-pd/scripts/driver-microkit.c. */
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>

extern lean_object *dregg_chokepoint_arrive(lean_object *wire);
extern lean_object *initialize_CommitBytes(uint8_t builtin);
extern void lean_initialize_runtime_module(void);

int chokepoint_init(void) {
    lean_initialize_runtime_module();
    lean_object *res = initialize_CommitBytes(1);
    if (lean_io_result_is_error(res)) {
        fputs("[commit]   FATAL: CommitBytes module init returned an IO error\n", stderr);
        lean_io_result_show_error(res);
        return 2;
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();
    return 0;
}

long chokepoint_arrive(const char *wire, unsigned long n, char *out, unsigned long cap) {
    lean_object *in = lean_mk_string_from_bytes(wire, (size_t)n);
    lean_object *r = dregg_chokepoint_arrive(in);
    const char *rc = lean_string_cstr(r);
    size_t rn = strlen(rc);
    long ret = -1;
    if (rn + 1 <= cap) {
        memcpy(out, rc, rn);
        out[rn] = 0;
        ret = (long)rn;
    }
    lean_dec_ref(r);
    return ret;
}
