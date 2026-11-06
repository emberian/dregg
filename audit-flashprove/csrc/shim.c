/* shim.c: the Lean embedding ritual and the byte-level wrappers around the exports of
 * minidregg Selvage/AuditFlashProveDecide.lean. No decision logic lives here: every wrapper
 * hands its arguments to one @[export]ed Lean function and returns its byte. */
#include <stdint.h>
#include <stddef.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_Selvage_AuditFlashProveDecide(uint8_t builtin);
extern uint8_t minidregg_fp_audit_fires(uint64_t, uint64_t);
extern uint8_t minidregg_fp_audit_verdict(uint8_t, lean_object *, uint8_t, uint32_t, lean_object *,
                                          lean_object *, uint32_t, uint32_t, uint8_t);
extern uint8_t minidregg_fp_audit_alarm(uint8_t, uint8_t);
extern uint8_t minidregg_fp_audit_alarm_open(uint8_t, uint8_t);

int fpaudit_init(void) {
  lean_initialize_runtime_module();
  lean_object *res = initialize_Selvage_AuditFlashProveDecide(1);
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  return 0;
}

uint8_t fpaudit_fires(uint64_t coin, uint64_t p_num) { return minidregg_fp_audit_fires(coin, p_num); }

uint8_t fpaudit_verdict(uint8_t open_ok, const char *out, size_t out_len, uint8_t has_exit, uint32_t exit_code,
                        const char *id, size_t id_len, const char *build, size_t build_len,
                        uint32_t r, uint32_t e, uint8_t accept_work) {
  /* Each String is owned by the callee (Lean's @[export] convention), so no dec_ref here. */
  return minidregg_fp_audit_verdict(open_ok, lean_mk_string_from_bytes(out, out_len), has_exit, exit_code,
                                    lean_mk_string_from_bytes(id, id_len),
                                    lean_mk_string_from_bytes(build, build_len), r, e, accept_work);
}

uint8_t fpaudit_alarm(uint8_t fired, uint8_t verdict) { return minidregg_fp_audit_alarm(fired, verdict); }

uint8_t fpaudit_alarm_open(uint8_t fired, uint8_t verdict) {
  return minidregg_fp_audit_alarm_open(fired, verdict);
}
