//! In-process event collector. The Studio inspector consumes the JSON the
//! `EventLog::to_json` produces; integration points in other crates can call
//! [`Emitter::emit`] to enqueue events without taking on a tracing dependency.

use std::cell::RefCell;
use std::rc::Rc;

use serde::Serialize;
use serde_json::Value;

use crate::events::TraceEvent;
use crate::schema::{SCHEMA_NAME, SCHEMA_VERSION};

/// An in-memory append-only log of trace events. Designed for single-process
/// observability; durability + concurrent emission are out of scope for the
/// seed crate (see crate-level docs).
#[derive(Debug, Default, Clone)]
pub struct EventLog {
    events: Vec<TraceEvent>,
}

impl EventLog {
    pub fn new() -> Self {
        Self::default()
    }

    /// Append an event.
    pub fn push(&mut self, event: TraceEvent) {
        self.events.push(event);
    }

    /// Borrow the events in emission order.
    pub fn events(&self) -> &[TraceEvent] {
        &self.events
    }

    /// Number of events in the log.
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Whether the log is empty.
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Render the event stream as a Studio-shape JSON document with header
    /// + ordered events array.
    pub fn to_json_value(&self) -> Value {
        serde_json::json!({
            "schema_version": SCHEMA_VERSION,
            "schema_name": SCHEMA_NAME,
            "event_count": self.events.len(),
            "events": self.events.iter().map(serialize_event).collect::<Vec<_>>(),
        })
    }

    /// Render as pretty-printed JSON string (Studio's preferred form).
    pub fn to_pretty_string(&self) -> String {
        serde_json::to_string_pretty(&self.to_json_value())
            .expect("event log JSON serialization must not fail")
    }
}

/// Serialize one event with its `kind` discriminator hoisted to a flat
/// top-level field — this is the Studio-side wire shape (see crate docs).
fn serialize_event(event: &TraceEvent) -> Value {
    // `TraceEvent` itself derives Serialize with `tag = "kind", content = "body"`.
    // We unwrap that into a flat `{ kind, envelope, payload }` form because
    // the body's content shape is already `{ envelope, payload }` and the
    // flat form is friendlier for Studio's TS bindings.
    let raw = serde_json::to_value(event).expect("event serializes");
    if let Some(obj) = raw.as_object() {
        if let (Some(kind), Some(body)) = (obj.get("kind"), obj.get("body")) {
            if let Some(body_obj) = body.as_object() {
                let envelope = body_obj.get("envelope").cloned().unwrap_or(Value::Null);
                let payload = body_obj.get("payload").cloned().unwrap_or(Value::Null);
                return serde_json::json!({
                    "kind": kind,
                    "envelope": envelope,
                    "payload": payload,
                });
            }
        }
    }
    raw
}

/// Cheap-to-clone emitter handle. Wraps a shared `RefCell<EventLog>`; designed
/// to be passed by clone into helpers that need to enqueue events without
/// threading a `&mut EventLog` through every call site.
///
/// Single-threaded by design — this matches the executor's request-scoped
/// access pattern. A concurrent emitter would replace the `Rc<RefCell<_>>`
/// with an `Arc<Mutex<_>>` (or a lock-free channel) without changing the
/// public API.
#[derive(Debug, Default, Clone)]
pub struct Emitter {
    inner: Rc<RefCell<EmitterState>>,
}

#[derive(Debug, Default)]
struct EmitterState {
    log: EventLog,
    next_seq: u64,
    /// Optional unix-millis clock override. When `None`, events use
    /// `unix_millis_now()` (a clock-less fallback that returns 0 in tests).
    clock: Option<Box<dyn Fn() -> i64>>,
}

impl Emitter {
    /// Construct an empty emitter.
    pub fn new() -> Self {
        Self::default()
    }

    /// Install a clock function. Used by the demo binary to get real
    /// wall-clock timestamps; tests can pin to a deterministic value.
    pub fn set_clock(&self, clock: impl Fn() -> i64 + 'static) {
        self.inner.borrow_mut().clock = Some(Box::new(clock));
    }

    /// Allocate the next sequence number + timestamp pair. Callers use this
    /// when constructing an envelope so seq is monotonic.
    pub fn next_envelope_seed(&self) -> (u64, i64) {
        let mut state = self.inner.borrow_mut();
        let seq = state.next_seq;
        state.next_seq += 1;
        let ts = match &state.clock {
            Some(clock) => clock(),
            None => 0,
        };
        (seq, ts)
    }

    /// Append an event to the log.
    pub fn emit(&self, event: TraceEvent) {
        self.inner.borrow_mut().log.push(event);
    }

    /// Snapshot the log (clones the underlying event vec).
    pub fn snapshot(&self) -> EventLog {
        self.inner.borrow().log.clone()
    }

    /// Number of events emitted so far.
    pub fn len(&self) -> usize {
        self.inner.borrow().log.len()
    }

    /// Whether any events have been emitted.
    pub fn is_empty(&self) -> bool {
        self.inner.borrow().log.is_empty()
    }
}

/// Helper for plumbing serialize-able structs through the emitter without
/// constructing the full `TraceEvent` tag tree by hand. Currently unused
/// but reserved for future ergonomic shorthand.
#[allow(dead_code)]
pub(crate) fn to_json<T: Serialize>(value: &T) -> Value {
    serde_json::to_value(value).expect("event payload serializes")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{EventBody, EventEnvelope, TurnLifecyclePayload};

    #[test]
    fn empty_log_serializes() {
        let log = EventLog::new();
        let v = log.to_json_value();
        assert_eq!(v["schema_version"], SCHEMA_VERSION);
        assert_eq!(v["event_count"], 0);
        assert!(v["events"].as_array().unwrap().is_empty());
    }

    #[test]
    fn emitter_increments_seq() {
        let em = Emitter::new();
        let (seq0, _) = em.next_envelope_seed();
        let (seq1, _) = em.next_envelope_seed();
        assert_eq!(seq0, 0);
        assert_eq!(seq1, 1);
    }

    #[test]
    fn event_serializes_with_kind_field() {
        let em = Emitter::new();
        let (seq, ts) = em.next_envelope_seed();
        em.emit(TraceEvent::TurnLifecycle(EventBody {
            envelope: EventEnvelope::new(seq, ts),
            payload: TurnLifecyclePayload::Expired,
        }));
        let snapshot = em.snapshot();
        let json = snapshot.to_json_value();
        let events = json["events"].as_array().unwrap();
        assert_eq!(events.len(), 1);
        assert_eq!(events[0]["kind"], "turn_lifecycle");
        assert_eq!(events[0]["envelope"]["seq"], 0);
        assert_eq!(events[0]["payload"]["phase"], "expired");
    }
}
