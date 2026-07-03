//! `dregg-sandbox` — the dregg-native execution sandbox.
//!
//! [`run_workload`] runs a workload at the sandbox grade a dregg lease authorizes.
//! The [`CapTier::Sandboxed`] tier is backed by an OWNED wasm engine — the
//! pure-Rust, zero-`unsafe` `wasmi` interpreter — instantiated against an EMPTY
//! [`wasmi::Linker`], so the guest is offered NO host imports and reaches nothing
//! on the host. The `add(40,2)=42` dogfood genuinely executes here.
//!
//! This is the dregg-native strip-mine of a prior exec module's one
//! genuinely-unique, load-bearing piece: the empty-Linker fail-closed wasmi engine
//! plus the [`CapTier`] tier-gate. Everything else that lived beside it in the old
//! crate — the budget/meter, the egress allowlist, the log capture, the execution
//! model descriptor — is ALREADY native and is NOT re-ported here:
//!
//! - budget / meter → [`dregg_agent::budget`] / [`dregg_agent::meter`].
//! - the egress **allowlist** (`EgressGrant` / `EgressPolicy`) → `deos-hermes::egress`
//!   (+ `deos-hermes::confined`, the SBPL/Landlock jail). See [egress](#egress).
//! - log capture → `a prior log sink` / `observability`.
//!
//! ## The tiers
//!
//! | [`CapTier`]              | lang           | backing                                   |
//! |--------------------------|----------------|-------------------------------------------|
//! | [`CapTier::Sandboxed`]   | `wasm`/`wat`   | OWNED wasmi interpreter (real execution)  |
//! | [`CapTier::JitSandboxed`]| `wasm`/`wat`   | honest fail-closed seam (owned JIT: TODO) |
//! | [`CapTier::Caged`]       | `native`/`bin` | honest fail-closed seam (owned OS sandbox)|
//! | [`CapTier::MicroVm`]     | any            | honest fail-closed seam (owned microVM)   |
//! | [`CapTier::Gpu`]         | any            | honest fail-closed seam (owned GPU VM)    |
//!
//! Only the [`CapTier::Sandboxed`] wasm tier has an owned engine linked today.
//! Every stronger tier — and the native interpreter langs (`python`/`node`) — is
//! an honest, fail-closed SEAM: the run refuses with [`RunError::TierNotServed`] /
//! [`RunError::NotWired`], naming exactly what an owned engine would back. It is
//! NEVER a silent downgrade to a weaker sandbox and NEVER a fake success. Wiring
//! an owned engine for each tier is future work.
//!
//! ## Default-deny is FAIL-CLOSED
//!
//! The wasmi tier instantiates against an EMPTY [`wasmi::Linker`]: the guest has
//! no host imports at all, so it reaches nothing on the host filesystem or
//! network, and a module that imports anything fails to *instantiate* rather than
//! running unsandboxed. The cap bundle a dregg lease carries is threaded at the
//! confined-agent gate (see [the toolkit adapter][crate::toolkit]); here the floor
//! is total deny.
//!
//! <a id="egress"></a>
//! ## Egress: deny-by-default, by construction
//!
//! For the one owned tier, "deny-by-default egress" is not a policy object this
//! crate evaluates — it is a STRUCTURAL property of the empty Linker. A wasm guest
//! reaches the network only through a host import; with no host import in the
//! Linker the guest holds no primitive that could open a socket, so egress is
//! denied *by construction* ([`EgressPosture::DenyByConstruction`], asserted by
//! the `sandboxed_denies_all_host_imports_fail_closed` test). The stronger tiers
//! run nothing at all yet, so they egress nothing ([`EgressPosture::NoEngineNoEgress`]).
//! When an owned engine that DOES expose host imports (a JIT tier, a microVM
//! netns) is wired, the destination-allowlist it must consult already lives
//! natively in `deos-hermes::egress` — this crate deliberately does not
//! re-implement it, because the wasm floor has no door to gate.
//!
//! ## Driving it from the confined-agent gate
//!
//! [`run_workload`] is the engine; it is not the authority. Cap-gating, metering,
//! and receipting live in [`dregg_agent::toolkit`], whose compute tools take an
//! injected runner. [`crate::toolkit::SandboxToolkit`] wires this engine in as
//! that runner, so an agent's `run_tests` / `run_workload` invoke runs on the
//! owned sandbox at a chosen tier — every run cap-gated + metered + receipted by
//! the open core, executed by this crate.

pub mod toolkit;

/// The sandbox / capability grade a workload is authorized to run at.
///
/// Maps onto the dregg execution-lease cap-grade. Ordered weakest → strongest
/// isolation. Only [`Sandboxed`](CapTier::Sandboxed) has an owned engine linked
/// today (the wasmi interpreter); the stronger tiers are honest fail-closed seams
/// (see the crate docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CapTier {
    /// In-process pure-interpreter wasm sandbox — the OWNED wasmi interpreter
    /// (`"WasmSandbox"`), no JIT, no fuel meter; the cheapest real sandbox and the
    /// one genuinely-executed tier. Consumes core-module wasm.
    Sandboxed,
    /// In-process JIT'd wasm sandbox (Cranelift-class codegen + a fuel meter +
    /// cap-gated host imports) — strictly stronger than
    /// [`Sandboxed`](CapTier::Sandboxed). No owned engine linked yet: an honest
    /// fail-closed seam. Would consume a component-model binary.
    JitSandboxed,
    /// Native process under seccomp + Landlock (`"OsSandbox"`) — a host binary run
    /// as a child process with a syscall + filesystem allowlist. No owned engine
    /// linked yet: an honest fail-closed seam. Would consume a `native`/`bin`
    /// workload, not wasm.
    Caged,
    /// Hardware-isolated microVM — a per-workload VM with its own guest kernel
    /// behind the KVM boundary (the fly.io / AWS-Lambda model). No owned engine
    /// linked yet: an honest fail-closed seam that refuses cleanly rather than
    /// downgrading.
    MicroVm,
    /// GPU / heavy-compute tier — a hardware-isolated VM with a passed-through GPU
    /// (whole device via VFIO, or an NVIDIA MIG slice), metered in GPU-seconds. No
    /// owned engine linked yet: an honest fail-closed seam that refuses cleanly
    /// (never a silent downgrade to CPU-only).
    Gpu,
}

impl CapTier {
    /// `true` for the one tier with an owned engine linked today
    /// ([`Sandboxed`](CapTier::Sandboxed)). Every other tier is a fail-closed seam.
    pub fn is_served(self) -> bool {
        matches!(self, CapTier::Sandboxed)
    }
}

/// The egress posture a run at a given [`CapTier`] has.
///
/// This crate does not evaluate a destination allowlist (that native machinery is
/// `deos-hermes::egress`); it reports the structural posture. See the crate-level
/// egress section in the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EgressPosture {
    /// The owned wasm tier: the guest runs against an EMPTY Linker, so it holds no
    /// host import and therefore no network primitive — egress is denied *by
    /// construction*, not by a policy check that could be misconfigured.
    DenyByConstruction,
    /// A fail-closed seam tier: no owned engine runs, so nothing egresses.
    NoEngineNoEgress,
}

/// The egress posture for a run at `tier`. Deny-by-default holds for every tier:
/// the served wasm tier denies by construction, the unserved tiers run nothing.
pub fn egress_posture(tier: CapTier) -> EgressPosture {
    match tier {
        CapTier::Sandboxed => EgressPosture::DenyByConstruction,
        _ => EgressPosture::NoEngineNoEgress,
    }
}

/// The result of running a workload: the values the entrypoint returned.
///
/// The entrypoint's return values are rendered to strings so callers don't take an
/// engine type in their signature.
///
/// `enforcement` is the isolation grade the workload *actually* ran under. It is
/// surfaced (never hidden) so a caller that requires a hard floor can inspect it —
/// a downgrade is made LOUD instead of silent. The owned wasmi tier reports
/// `"WasmSandbox"`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Output {
    /// The entrypoint's return values, rendered to strings.
    pub values: Vec<String>,
    /// The enforcement level the run actually achieved (e.g. `"WasmSandbox"`).
    pub enforcement: String,
}

/// The enforcement label the owned wasmi interpreter reports.
const WASM_SANDBOX: &str = "WasmSandbox";

/// A typed input value handed to a workload's entrypoint.
///
/// This is the real input convention: a workload receives actual argument values
/// (numbers / text), NOT constants spliced into its source text.
///
/// - The owned wasm tier (wasmi) accepts the **numeric** variants ([`Input::I32`],
///   [`Input::I64`], [`Input::F32`], [`Input::F64`]); it is numeric-only.
/// - The [`Input::Text`] variant is for the native interpreter tiers (an honest
///   seam today) — it carries a real string, not an integer-only query param. (The
///   old crate also carried a `Json` variant for those tiers; it is dropped here
///   until a native tier gains an owned engine, keeping this crate free of a JSON
///   dep it would not use.)
#[derive(Debug, Clone, PartialEq)]
pub enum Input {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    Text(String),
}

impl Input {
    /// `true` for the numeric variants the core-wasm ABI passes directly to a
    /// wasmi entrypoint. The wasm tier is numeric-only; string args are refused up
    /// front (they belong to the not-yet-owned native tiers).
    fn is_numeric(&self) -> bool {
        matches!(
            self,
            Input::I32(_) | Input::I64(_) | Input::F32(_) | Input::F64(_)
        )
    }

    /// Lower a numeric input to the [`wasmi::Val`] the entrypoint receives. Only
    /// numeric variants reach here (callers gate on [`Input::is_numeric`]).
    fn to_val(&self) -> wasmi::Val {
        match self {
            Input::I32(n) => wasmi::Val::I32(*n),
            Input::I64(n) => wasmi::Val::I64(*n),
            Input::F32(f) => wasmi::Val::F32((*f).into()),
            Input::F64(f) => wasmi::Val::F64((*f).into()),
            // Non-numeric variants are rejected before lowering.
            Input::Text(_) => wasmi::Val::I32(0),
        }
    }
}

/// A typed execution error — an engine failure surfaces as one of these clean
/// categories rather than a bare string, panic, or hang.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum RunError {
    /// No provider family wired for this `lang`.
    #[error("no execution engine wired for lang `{0}`")]
    UnsupportedLang(String),
    /// The requested tier has no owned engine linked (a fail-closed seam), naming
    /// exactly what an owned engine would back — never a silent downgrade.
    #[error("cap-tier {tier:?} is not served: {detail}")]
    TierNotServed { tier: CapTier, detail: String },
    /// An argument's type isn't accepted by the selected tier (e.g. a string
    /// passed to the numeric-only wasmi interpreter).
    #[error("{tier}: unsupported argument: {detail}")]
    UnsupportedArg { tier: &'static str, detail: String },
    /// WAT / source assembly failed.
    #[error("source assembly failed: {0}")]
    Assembly(String),
    /// Decoding the module bytes failed (bad wasm).
    #[error("module load failed: {0}")]
    Load(String),
    /// `instantiate` failed — e.g. the module imports a host function the EMPTY
    /// Linker does not provide (fail-closed: it does NOT run unsandboxed).
    #[error("instantiate failed: {0}")]
    Instantiate(String),
    /// The entrypoint was missing, or the guest trapped during the call.
    #[error("workload call failed: {0}")]
    Call(String),
    /// A lang whose family has no owned execution engine linked (fail-closed; no
    /// unsandboxed fallback is run).
    #[error("{0}")]
    NotWired(String),
}

/// The conventional entrypoint a dregg workload exports (`run`).
const ENTRYPOINT: &str = "run";

/// Run one workload at the authorized cap tier, on already-assembled core-wasm
/// module bytes, passing real argument values to its `run` entrypoint.
///
/// This is the engine's front door: `tier` is the sandbox grade the dregg lease
/// authorizes, `module` is the core-wasm binary, and `input` is the argument
/// vector handed to `run`.
///
/// - [`CapTier::Sandboxed`] runs `module` on the OWNED wasmi interpreter (numeric
///   args only) against an EMPTY Linker — the genuinely-executed tier.
/// - Every stronger tier ([`CapTier::JitSandboxed`], [`CapTier::Caged`],
///   [`CapTier::MicroVm`], [`CapTier::Gpu`]) is an honest, fail-closed SEAM:
///   [`RunError::TierNotServed`], naming what an owned engine would back — never a
///   silent downgrade to a weaker sandbox and never a fake run.
///
/// For WAT text or lang-dispatch (the shape the confined-agent gate injects), use
/// [`run_source`].
pub fn run_workload(tier: CapTier, module: &[u8], input: &[Input]) -> Result<Output, RunError> {
    wasm_tier_gate(tier)?;
    run_on_wasmi(module, input)
}

/// Run one workload from source text, selecting the tier family by `lang`.
///
/// `"wasm"`/`"wat"` at [`CapTier::Sandboxed`] assembles the source to core-wasm and
/// runs it on the owned wasmi interpreter. The native interpreter langs
/// (`python`/`node`/`native`/`bin`) are honest, fail-closed seams
/// ([`RunError::NotWired`]); an unknown lang is [`RunError::UnsupportedLang`]. Every
/// stronger wasm tier is a seam exactly as in [`run_workload`].
///
/// This is the shape [`crate::toolkit::SandboxToolkit`] injects into the
/// confined-agent gate (the runner seam takes `(lang, source)`).
pub fn run_source(
    lang: &str,
    source: &str,
    tier: CapTier,
    input: &[Input],
) -> Result<Output, RunError> {
    match lang {
        "wasm" | "wat" => {
            // Gate the tier BEFORE assembling, so a not-served tier refuses cleanly
            // rather than surfacing a WAT parse error for a run that would never
            // have executed here anyway.
            wasm_tier_gate(tier)?;
            let module = wat::parse_str(source).map_err(|e| RunError::Assembly(e.to_string()))?;
            run_on_wasmi(&module, input)
        }
        "python" | "py" | "node" | "js" | "native" | "bin" => Err(RunError::NotWired(format!(
            "dregg-sandbox: the `{lang}` tier has no owned execution engine linked (owned \
             native/interpreter sandboxed execution is future work); the owned, genuinely-executed \
             tier is `wasm`/`wat` at CapTier::Sandboxed. No unsandboxed fallback is run \
             (fail-closed)"
        ))),
        other => Err(RunError::UnsupportedLang(other.to_string())),
    }
}

/// The tier-gate for a wasm workload: [`CapTier::Sandboxed`] is served by the owned
/// wasmi interpreter; every stronger tier is an honest fail-closed seam naming what
/// an owned engine would back. Never a silent downgrade.
fn wasm_tier_gate(tier: CapTier) -> Result<(), RunError> {
    match tier {
        CapTier::Sandboxed => Ok(()),
        CapTier::JitSandboxed => Err(RunError::TierNotServed {
            tier,
            detail: "the JitSandboxed (JIT wasm) tier has no owned engine linked; the owned \
                     Sandboxed (wasmi interpreter) tier runs core-module wasm today, and an owned \
                     JIT engine is future work — never a silent downgrade to the weaker tier"
                .into(),
        }),
        CapTier::Caged => Err(RunError::TierNotServed {
            tier,
            detail:
                "the Caged (native-under-seccomp+Landlock) tier has no owned engine linked and \
                     would consume a native/bin workload, not wasm; owned OS-sandbox execution is \
                     future work (no weaker tier is substituted)"
                    .into(),
        }),
        CapTier::MicroVm => Err(RunError::TierNotServed {
            tier,
            detail: "the MicroVm tier (a per-workload hardware-isolated VM) has no owned engine \
                     linked; owned microVM execution is future work. No weaker tier is substituted \
                     (no silent downgrade)"
                .into(),
        }),
        CapTier::Gpu => Err(RunError::TierNotServed {
            tier,
            detail: "the Gpu tier (a GPU-passthrough VM) has no owned engine linked; owned GPU \
                     execution is future work. No CPU-only backend is substituted (no silent \
                     downgrade)"
                .into(),
        }),
    }
}

/// Run core-wasm `module` bytes on the OWNED wasmi interpreter — the
/// [`CapTier::Sandboxed`] tier.
///
/// wasmi is a pure-Rust, zero-`unsafe` wasm interpreter. The module is instantiated
/// against an EMPTY [`wasmi::Linker`]: the guest is offered NO host imports, so it
/// reaches nothing on the host filesystem or network (deny-all, fail-closed, and
/// therefore egress denied by construction). A module that imports anything fails
/// to instantiate rather than running unsandboxed. The dregg lease's real caps are
/// threaded at the confined-agent gate.
fn run_on_wasmi(module: &[u8], input: &[Input]) -> Result<Output, RunError> {
    use wasmi::{Engine, Linker, Module, Store, Val};

    // The core-wasm ABI is numeric-only; reject string args up front with a clean
    // message rather than a deep engine error.
    if let Some(bad) = input.iter().find(|a| !a.is_numeric()) {
        return Err(RunError::UnsupportedArg {
            tier: "wasmi (Sandboxed)",
            detail: format!(
                "core wasm accepts numeric args only; got {bad:?} — string args belong to the \
                 not-yet-owned native tiers"
            ),
        });
    }

    let engine = Engine::default();
    let module = Module::new(&engine, module).map_err(|e| RunError::Load(e.to_string()))?;

    let mut store = Store::new(&engine, ());
    // Empty linker = deny-all host surface. No host import is offered, so a module
    // that requests one fails to instantiate (fail-closed), and a module that runs
    // has no primitive to reach the host / the network.
    let linker = Linker::<()>::new(&engine);
    let instance = linker
        .instantiate(&mut store, &module)
        .and_then(|pre| pre.start(&mut store))
        .map_err(|e| RunError::Instantiate(e.to_string()))?;

    let func = instance
        .get_func(&store, ENTRYPOINT)
        .ok_or_else(|| RunError::Call(format!("export `{ENTRYPOINT}` not found")))?;

    let args: Vec<Val> = input.iter().map(Input::to_val).collect();
    let n_results = func.ty(&store).results().len();
    let mut results = vec![Val::I32(0); n_results];
    func.call(&mut store, &args, &mut results)
        .map_err(|e| RunError::Call(e.to_string()))?;

    Ok(Output {
        values: results.iter().map(val_to_string).collect(),
        enforcement: WASM_SANDBOX.to_string(),
    })
}

/// Render a wasmi [`wasmi::Val`] to the string surface a run returns.
fn val_to_string(v: &wasmi::Val) -> String {
    match v {
        wasmi::Val::I32(n) => n.to_string(),
        wasmi::Val::I64(n) => n.to_string(),
        wasmi::Val::F32(f) => f.to_float().to_string(),
        wasmi::Val::F64(f) => f.to_float().to_string(),
        other => format!("{other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The core-module WAT dogfood: `run` calls an inner `add` on 40 and 2 and
    /// returns 42 — the `i32.add` genuinely executes inside the OWNED wasmi sandbox.
    fn add_40_2_wat() -> &'static str {
        r#"
            (module
              (func $add (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add)
              (func (export "run") (result i32)
                (call $add (i32.const 40) (i32.const 2))))
        "#
    }

    #[test]
    fn dogfood_add_40_2_equals_42_on_owned_wasmi() {
        let out = run_source("wat", add_40_2_wat(), CapTier::Sandboxed, &[])
            .expect("owned wasmi should run the add dogfood");
        assert_eq!(out.values, vec!["42".to_string()]);
        assert_eq!(out.enforcement, "WasmSandbox");
    }

    #[test]
    fn run_workload_runs_assembled_module_bytes() {
        // The `module_bytes` front door: assemble once, then run the raw core-wasm.
        let module = wat::parse_str(add_40_2_wat()).expect("assemble");
        let out = run_workload(CapTier::Sandboxed, &module, &[])
            .expect("owned wasmi should run assembled bytes");
        assert_eq!(out.values, vec!["42".to_string()]);
        assert_eq!(out.enforcement, "WasmSandbox");
    }

    #[test]
    fn wasmi_receives_real_numeric_args() {
        // `run(a, b) = a + b`, invoked with real call arguments.
        let src = r#"
            (module
              (func (export "run") (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add))
        "#;
        let out = run_source(
            "wat",
            src,
            CapTier::Sandboxed,
            &[Input::I32(40), Input::I32(2)],
        )
        .expect("owned wasmi should pass numeric args");
        assert_eq!(out.values, vec!["42".to_string()]);
    }

    #[test]
    fn wasmi_rejects_non_numeric_args() {
        let err = run_source(
            "wat",
            add_40_2_wat(),
            CapTier::Sandboxed,
            &[Input::Text("nope".into())],
        )
        .expect_err("wasmi is numeric-only");
        assert!(
            matches!(err, RunError::UnsupportedArg { .. }),
            "got {err:?}"
        );
    }

    #[test]
    fn wasmi_missing_run_export_is_a_clean_error() {
        let src = r#"(module (func (export "other") (result i32) (i32.const 1)))"#;
        let err = run_source("wat", src, CapTier::Sandboxed, &[]).expect_err("no `run` export");
        assert!(err.to_string().contains("run"), "got {err}");
    }

    /// Deny-by-construction egress + fail-closed host imports in one: a module that
    /// imports ANY host function cannot instantiate against the EMPTY Linker — it
    /// fails closed rather than running unsandboxed. Because the only way a wasm
    /// guest could egress is a host import, this is exactly the egress-deny proof.
    #[test]
    fn sandboxed_denies_all_host_imports_fail_closed() {
        let src = r#"
            (module
              (import "env" "sneak" (func $sneak))
              (func (export "run") (result i32) (i32.const 0)))
        "#;
        let err =
            run_source("wat", src, CapTier::Sandboxed, &[]).expect_err("host imports are denied");
        let msg = err.to_string().to_lowercase();
        assert!(
            msg.contains("instantiate") || msg.contains("import") || msg.contains("missing"),
            "got {err}"
        );
        // The posture the crate reports for the served tier is deny-by-construction.
        assert_eq!(
            egress_posture(CapTier::Sandboxed),
            EgressPosture::DenyByConstruction
        );
    }

    // --- The stronger tiers are honest, fail-closed seams (no owned engine yet) ---

    #[test]
    fn jit_tier_is_an_honest_seam() {
        let err = run_source("wat", add_40_2_wat(), CapTier::JitSandboxed, &[])
            .expect_err("JIT tier is not wired");
        assert!(matches!(err, RunError::TierNotServed { .. }), "got {err:?}");
        assert!(err.to_string().contains("JitSandboxed"), "got {err}");
    }

    #[test]
    fn microvm_tier_is_an_honest_seam() {
        let module = wat::parse_str(add_40_2_wat()).expect("assemble");
        let err = run_workload(CapTier::MicroVm, &module, &[]).expect_err("MicroVm is not wired");
        assert!(matches!(err, RunError::TierNotServed { .. }), "got {err:?}");
        assert_eq!(
            egress_posture(CapTier::MicroVm),
            EgressPosture::NoEngineNoEgress
        );
    }

    #[test]
    fn gpu_tier_is_an_honest_seam() {
        let module = wat::parse_str(add_40_2_wat()).expect("assemble");
        let err = run_workload(CapTier::Gpu, &module, &[]).expect_err("Gpu is not wired");
        assert!(matches!(err, RunError::TierNotServed { .. }), "got {err:?}");
    }

    #[test]
    fn caged_and_native_langs_are_honest_seams() {
        for lang in ["python", "py", "node", "js", "native", "bin"] {
            let err =
                run_source(lang, "x", CapTier::Caged, &[]).expect_err("native tiers are not wired");
            assert!(matches!(err, RunError::NotWired(_)), "{lang}: got {err:?}");
        }
        // A wasm workload asked for the Caged tier is a served-lang / unserved-tier
        // seam (TierNotServed), distinct from the unknown-lang case above.
        let err = run_source("wat", add_40_2_wat(), CapTier::Caged, &[])
            .expect_err("wasm at Caged is not wired");
        assert!(matches!(err, RunError::TierNotServed { .. }), "got {err:?}");
    }

    #[test]
    fn unknown_lang_is_refused() {
        let err = run_source("ruby", "x", CapTier::Sandboxed, &[]).expect_err("no ruby tier");
        assert!(matches!(err, RunError::UnsupportedLang(_)), "got {err:?}");
        assert!(err.to_string().contains("ruby"), "got {err}");
    }

    #[test]
    fn served_tier_is_only_sandboxed() {
        assert!(CapTier::Sandboxed.is_served());
        for t in [
            CapTier::JitSandboxed,
            CapTier::Caged,
            CapTier::MicroVm,
            CapTier::Gpu,
        ] {
            assert!(!t.is_served(), "{t:?} should be a fail-closed seam");
        }
    }
}
