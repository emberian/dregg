// build.rs — wire the Rust binary to the compiled Lean kernel + Lean runtime.
//
// We link against:
//   * libdregg_lean.a — a single static archive of the native objects emitted by the
//     Lean compiler for `Dregg2.Exec.FFI` and its ENTIRE transitive dependency
//     closure (Dregg2 modules + mathlib + batteries + aesop + Qq + … — ~8200 .o).
//     The git-tracked SEED archive lives next to this build.rs; it was produced by
//     compiling each module's `.c` (lake's `:c` facet) with `leanc -c` and archiving
//     with `llvm-ar` (see `scripts/seed-dregg2-closure.sh`).
//
// ── SWARM-SAFE ARCHIVE (the per-OUT_DIR working copy) ──
// The git-tracked `libdregg_lean.a` is treated as a READ-ONLY SEED. A `cargo build`
// NEVER mutates it. Instead, each build copies the seed into a per-`OUT_DIR` working
// archive (`$OUT_DIR/libdregg_lean.a`) and does its splice → closure-completion →
// reachability-GC against THAT copy, then links against it. Because `OUT_DIR` is
// per-(crate, feature-set, profile) — cargo's own fingerprint dir — concurrent lanes
// with DIFFERENT feature sets each splice/prune their OWN archive and never tear a
// shared file. (Before this split the shared seed was rewritten from every build
// script invocation: two concurrent multi-feature lanes raced it into a torn /
// wrong-feature archive → `Undefined symbols: _initialize_Dregg2_*` across the swarm.)
// The seed is (re)produced ONLY out-of-band by `scripts/seed-dregg2-closure.sh` /
// `scripts/rebuild-dregg2-closure.sh` — never by a `cargo build`.
//   * the Lean runtime + stdlib in the elan toolchain `lib/lean` dir — STATIC by default
//     (leancpp/Init/Std/Lean/leanrt + gmp/uv/c++), or SHARED (libleanshared + Lake_shared)
//     when `DREGG_LEAN_LINK=shared` (the cdylib link mode, see `shared_link_mode`).
//
// Toolchain paths are discovered from `lake env` (LEAN_SYSROOT) with a fallback to the
// pinned elan toolchain, so this stays robust to elan being on PATH.

use std::path::{Path, PathBuf};
use std::process::Command;

// ── ARCHIVE-TOOL NAMES (the binutils trio) ──────────────────────────────────────
// The archive splice / closure-completion / reachability-GC below shell out to the
// `ar` / `nm` / `ranlib` trio. On macOS / Linux these resolve to the host binutils
// (or their llvm aliases) on PATH — UNCHANGED. On Windows the Lean toolchain is the
// LLVM-MinGW distribution (`x86_64-w64-windows-gnu`): its archives are GNU `.a` of
// `coff-x86-64` objects, read/written by `llvm-ar` and inspected by `llvm-nm` (plain
// `ar`/`nm`/`ranlib` are not on a stock Windows PATH). These helpers centralise the
// name so every `Command::new(ar_tool())` etc. picks the right binary per-OS. On
// non-Windows they return exactly `"ar"`/`"nm"`/`"ranlib"`, so the unix paths are
// byte-identical to before. See `windows_gnu_link_env` for the matching link arm.
fn ar_tool() -> &'static str {
    if cfg!(windows) {
        "llvm-ar"
    } else {
        "ar"
    }
}
fn nm_tool() -> &'static str {
    if cfg!(windows) {
        "llvm-nm"
    } else {
        "nm"
    }
}
/// `ranlib` regenerates an archive's symbol index. `llvm-ar` writes the index on
/// every `rcs`/`r` op (and `llvm-ranlib` may not be on PATH), so on Windows we run
/// `llvm-ar s <archive>` — the explicit "regenerate symbol table" op — instead.
fn run_ranlib(archive: &Path) -> std::io::Result<std::process::ExitStatus> {
    if cfg!(windows) {
        Command::new(ar_tool()).arg("s").arg(archive).status()
    } else {
        Command::new("ranlib").arg(archive).status()
    }
}

/// Locate the project's `metatheory` Lean directory relative to this crate, so
/// `lake env` runs against the project's pinned toolchain regardless of the host
/// (no hardcoded absolute paths — works on macOS dev boxes and the Linux deploy
/// box alike). `CARGO_MANIFEST_DIR` is `.../dregg-lean-ffi`; the sibling is
/// `.../metatheory`. An explicit `DREGG_METATHEORY_DIR` override wins if set.
fn metatheory_dir() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("DREGG_METATHEORY_DIR") {
        let p = PathBuf::from(dir);
        if p.join("lean-toolchain").exists() {
            return Some(p);
        }
    }
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let candidate = crate_dir.parent().map(|p| p.join("metatheory"));
    candidate.filter(|p| p.join("lean-toolchain").exists())
}

fn lean_sysroot() -> Option<PathBuf> {
    // Prefer `lake env` (authoritative for the project's toolchain). `DREGG_LEAN_SYSROOT`
    // overrides for environments where `lake` is not on PATH at build time.
    if let Ok(s) = std::env::var("DREGG_LEAN_SYSROOT") {
        if !s.trim().is_empty() {
            return Some(PathBuf::from(s.trim()));
        }
    }
    if let Some(meta) = metatheory_dir() {
        if let Ok(out) = Command::new("lake")
            .args(["env", "printenv", "LEAN_SYSROOT"])
            .current_dir(&meta)
            .output()
        {
            let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if !s.is_empty() {
                return Some(PathBuf::from(s));
            }
        }
    }
    None
}

/// Flatten an IR-relative `.c` path into the splice object name the archive uses, matching the
/// shell script: `Dregg2/Exec/FFI.c` → `Dregg2_Exec_FFI.o` (path separators → `_`). Keeping the
/// exact same naming is what lets us REPLACE (not duplicate) the old Dregg2 members on re-splice.
fn splice_obj_name(ir_root: &Path, c: &Path) -> String {
    let rel = c.strip_prefix(ir_root).unwrap_or(c);
    let stem = rel.with_extension("");
    let mut name: String = stem
        .components()
        .map(|comp| comp.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("_");
    name.push_str(".o");
    name
}

/// `true` iff `target` is missing or older than `src` (the "recompile this" predicate — mirrors the
/// script's `[ ! -f "$out" ] || [ "$c" -nt "$out" ]`). Treats unreadable mtimes as "stale" so we
/// fail toward recompiling rather than shipping a stale object.
fn newer_than(src: &Path, target: &Path) -> bool {
    let Ok(target_meta) = std::fs::metadata(target) else {
        return true;
    };
    let (Ok(src_m), Ok(tgt_m)) = (
        std::fs::metadata(src).and_then(|m| m.modified()),
        target_meta.modified(),
    ) else {
        return true;
    };
    src_m > tgt_m
}

/// Recursively collect every regular file under `dir` (used to emit `rerun-if-changed` for the
/// whole Lean `Dregg2` source tree, so a no-op cargo build truly skips the closure rebuild).
fn collect_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_files(&path, out);
        } else {
            out.push(path);
        }
    }
}

/// Seed the per-OUT_DIR WORKING archive (`build`) from the git-tracked SEED (`seed`), so the
/// splice/closure/GC steps below mutate the working copy and NEVER the shared seed (the swarm-safe
/// split — see the top-of-file note). The seed is treated as read-only input.
///
/// We (re)copy when the working archive is missing OR older than the seed (an out-of-band re-seed
/// via `scripts/seed-dregg2-closure.sh` must take effect). When the working copy is at least as new
/// as the seed we leave it — its spliced Dregg2 slice + GC pruning are the incremental steady state
/// for THIS feature set and must survive a no-op rebuild. The copy is staged to a sibling temp and
/// renamed into place so a working archive is never observed half-written. If the seed is absent we
/// do nothing: a prior working copy (if any) is reused; otherwise the `!build_archive.exists()`
/// guard in `main` degrades to marshal-only.
fn seed_build_archive(seed: &Path, build: &Path) {
    if !seed.exists() {
        return;
    }
    // Decide whether to (re)seed. Copy iff the working archive is missing or strictly older than
    // the seed (mtime). `newer_than(seed, build)` ⇒ seed is newer (or build absent) ⇒ copy.
    if build.exists() && !newer_than(seed, build) {
        return;
    }
    let Some(parent) = build.parent() else {
        return;
    };
    // Stage to a unique-ish temp in the SAME dir (so the final rename is same-filesystem & atomic),
    // keyed on the build OUT_DIR's own path hash via the process id — one build script runs per
    // OUT_DIR at a time, but this keeps a crashed prior attempt from colliding.
    let tmp = parent.join(format!("libdregg_lean.a.seed-tmp.{}", std::process::id()));
    let _ = std::fs::remove_file(&tmp);
    match std::fs::copy(seed, &tmp) {
        Ok(_) => {}
        Err(e) => {
            println!(
                "cargo:warning=dregg-lean-ffi: could not stage the seed copy into OUT_DIR ({e}) — \
                 the build will use the existing working archive if present."
            );
            let _ = std::fs::remove_file(&tmp);
            return;
        }
    }
    if let Err(e) = std::fs::rename(&tmp, build) {
        // Same-dir rename should never cross devices; fall back to a copy if it somehow fails.
        if std::fs::copy(&tmp, build).is_err() {
            println!(
                "cargo:warning=dregg-lean-ffi: could not install the working archive in OUT_DIR \
                 ({e}) — using the existing working archive if present."
            );
        }
        let _ = std::fs::remove_file(&tmp);
    }
}

/// Produce / refresh `libdregg_lean.a` IN OUT_DIR by (1) `lake build`-ing the FFI module's
/// `:c` facet, (2) `leanc -c`-compiling each freshly-emitted `Dregg2/**/*.c` whose `.c` is newer
/// than its cached `.o`, and (3) splicing ONLY those `Dregg2_*.o` back into the (seeded) working
/// archive — preserving the ~5600 expensive mathlib/batteries/aesop dependency objects untouched.
/// `archive` here is the PER-OUT_DIR working copy, never the git-tracked seed.
///
/// Incremental + cached: `lake` is itself incremental, the `leanc` step is guarded on
/// `.c`-newer-than-`.o`, and the (relatively expensive) `ar` extract/repack only runs when at least
/// one Dregg2 object actually changed or the archive lacks Dregg2 members. `rerun-if-changed` is
/// emitted by the caller for the source tree + toolchain marker, so a genuine no-op cargo build does
/// not even re-enter this function.
fn build_dregg2_archive(meta: &Path, sysroot: &Path, archive: &Path, out_dir: &Path, seed: &Path) {
    // (1) Refresh the Lean `:c` facets. `lake build` is incremental; building the FFI module pulls
    // in (and emits `:c` for) its whole Dregg2 transitive closure.
    let inc = sysroot.join("include");
    let ir_root = meta.join(".lake/build/ir");
    let dregg2_ir = ir_root.join("Dregg2");

    // We build `Dregg2.Exec.FFI` (the executor exports) PLUS the verified-gate modules that live
    // OUTSIDE its import closure — `Dregg2.Distributed.{FinalityGate,StrandAdmission}` and
    // `Dregg2.Exec.DistributedExports` (the CapTP+coord decision gates). The splice compiles every
    // `Dregg2/**/*.c` present in the IR tree, so each of these must be `lake build`-t for its `.c` to
    // exist and be spliced in. Building them explicitly here (rather than relying on a prior full
    // `lake build` of the root) is what lets a FRESH lane (e.g. a persvati build dir with no warm
    // `.lake`) still emit and splice the gate exports. Each is incremental: an already-built module is
    // a no-op. A failure on one is non-fatal — we splice whatever `:c` facets exist.
    let lake_targets = [
        "Dregg2.Exec.FFI",
        "Dregg2.Distributed.FinalityGate",
        "Dregg2.Distributed.StrandAdmission",
        "Dregg2.Exec.DistributedExports",
        // The verified FLOW-REFINEMENT DECISION export (`dregg_decide_refines`) lives in
        // `Dregg2.Deos.FlowRefine`, also OUTSIDE the FFI import closure. Build it so its `.c` IR is
        // emitted and the `dregg_decide_refines` symbol is spliced in — the deploy gate
        // (`dregg-deploy/src/refine.rs`) calls it to run the PROVEN `decideRefines` instead of a mirror.
        "Dregg2.Deos.FlowRefine",
        // The NO-COPY (`lean_object*`) direct boundary builders/readers + the `execDirect` export
        // (`Dregg2.Exec.FFIDirect`). It IMPORTS `Dregg2.Exec.FFI`, so building FFI already pulls it
        // into the IR closure — but list it explicitly so a fresh lane with a cold `.lake` emits its
        // `.c` and the splice picks up the `dregg_exec_full_forest_auth_direct` + `dregg_d_*` symbols.
        "Dregg2.Exec.FFIDirect",
    ];
    let lake_status = Command::new("lake")
        .arg("build")
        .args(lake_targets)
        .current_dir(meta)
        .status();
    match lake_status {
        Ok(s) if s.success() => {}
        Ok(s) => {
            // `lake build` FAILED. When this happens the metatheory `.lake/build/ir` tree is NOT
            // guaranteed internally coherent: some modules' `:c` facets are freshly re-emitted while
            // others (the ones whose module elaboration aborted — e.g. a WIP proof regression tripping
            // an `#assert_axioms` hygiene gate) keep their STALE `.c` or have none at all. Splicing
            // that partial fresh set over the seed produces a torn archive whose cross-module
            // SPECIALIZATIONS don't resolve: a freshly-recompiled `Dregg2_Exec_Handler.o` references
            // `_lp_…_TurnExecutorFull_*` specialized symbols that the un-rebuilt `TurnExecutorFull.o`
            // never emitted → `Undefined symbols` at the final link of every downstream binary
            // (dregg-node included). The git-tracked SEED archive is, by construction, a coherent
            // linkable set. So on a `lake build` failure we DISCARD any prior (possibly incoherent)
            // working archive and restore the consistent seed, then skip the recompile/splice
            // entirely. The node links the known-good verified kernel; an in-progress metatheory
            // proof regression no longer blocks the node from running.
            println!(
                "cargo:warning=dregg-lean-ffi: `lake build` of the FFI + gate modules exited {s} — \
                 the metatheory IR tree may be incoherent (a module failed to elaborate). Restoring \
                 the git-tracked consistent seed archive and NOT splicing a partial fresh set (a torn \
                 splice would fail to link). To pick up fresh Lean changes, make `lake build \
                 Dregg2.Exec.FFI` green in metatheory/ and rebuild."
            );
            // Force the working archive back to the seed (overwrite any prior incoherent splice).
            let _ = std::fs::remove_file(archive);
            seed_build_archive(seed, archive);
            return;
        }
        Err(e) => {
            println!(
                "cargo:warning=dregg-lean-ffi: could not run `lake build` ({e}) — is elan/lake on \
                 PATH? Falling back to the existing archive (if any)."
            );
            return;
        }
    }

    // The `:c` facet must have landed for us to compile anything.
    if !dregg2_ir.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: no `:c` IR at {} after `lake build` — cannot compile the \
             Dregg2 native objects. Run `lake build Dregg2.Exec.FFI` in metatheory and re-check.",
            dregg2_ir.display()
        );
        return;
    }

    // Persistent object cache (so the `.c`-newer-than-`.o` guard survives across cargo builds).
    let obj_dir = out_dir.join("dregg2_closure_objs");
    if let Err(e) = std::fs::create_dir_all(&obj_dir) {
        println!(
            "cargo:warning=dregg-lean-ffi: cannot create {} ({e})",
            obj_dir.display()
        );
        return;
    }

    // (2) Compile each Dregg2 `.c` newer than its cached `.o`, in parallel up to the CPU count.
    let mut c_files = Vec::new();
    collect_files(&dregg2_ir, &mut c_files);
    c_files.retain(|p| p.extension().map(|e| e == "c").unwrap_or(false));
    c_files.sort();

    // The exact set of object names we expect from the CURRENT source. Used to (a) drive the
    // splice and (b) prune STALE cached objects whose `.c` was deleted/renamed — otherwise a
    // removed module's old `Dregg2_*.o` would keep getting spliced back in (dangling/duplicate
    // symbols). We treat such a prune as a change so the splice picks up the removal.
    let expected: std::collections::HashSet<String> = c_files
        .iter()
        .map(|c| splice_obj_name(&ir_root, c))
        .collect();
    let mut pruned = false;
    if let Ok(entries) = std::fs::read_dir(&obj_dir) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if name.starts_with("Dregg2_") && name.ends_with(".o") && !expected.contains(&name) {
                let _ = std::fs::remove_file(entry.path());
                pruned = true;
            }
        }
    }

    let mut jobs: Vec<(PathBuf, PathBuf)> = Vec::new();
    for c in &c_files {
        let obj = obj_dir.join(splice_obj_name(&ir_root, c));
        if newer_than(c, &obj) {
            jobs.push((c.clone(), obj));
        }
    }

    let recompiled = !jobs.is_empty() || pruned;
    if !jobs.is_empty() {
        println!(
            "cargo:warning=dregg-lean-ffi: compiling {} changed Dregg2 C facet(s) via leanc …",
            jobs.len()
        );
        let ncpu = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .max(1);
        let failed = std::sync::atomic::AtomicBool::new(false);
        let jobs_ref = &jobs;
        let next = std::sync::atomic::AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..ncpu {
                scope.spawn(|| {
                    loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        let Some((c, obj)) = jobs_ref.get(i) else {
                            break;
                        };
                        // `-fPIC` so the spliced objects are position-independent: the SAME archive
                        // then serves both link modes (static bins AND the `DREGG_LEAN_LINK=shared`
                        // cdylib link, e.g. the sdk-py pyo3 module). No-op on macOS (PIC is the
                        // default); on Linux it guards against a leanc default change (leanc
                        // currently compiles PIC there too — Lean plugins are dlopen'd).
                        let status = Command::new("lake")
                            .args(["env", "leanc", "-c", "-fPIC", "-I"])
                            .arg(&inc)
                            .arg(c)
                            .arg("-o")
                            .arg(obj)
                            .current_dir(meta)
                            .status();
                        let ok = matches!(status, Ok(s) if s.success());
                        if !ok {
                            // Drop a stale/partial object so the next build retries this `.c`.
                            let _ = std::fs::remove_file(obj);
                            failed.store(true, std::sync::atomic::Ordering::SeqCst);
                            println!(
                                "cargo:warning=dregg-lean-ffi: leanc failed on {}",
                                c.display()
                            );
                        }
                    }
                });
            }
        });
        if failed.load(std::sync::atomic::Ordering::SeqCst) {
            println!(
                "cargo:warning=dregg-lean-ffi: at least one Dregg2 C facet failed to compile — \
                 NOT re-splicing the archive (it keeps its previous, consistent contents)."
            );
            return;
        }
    }

    // (3) Splice. Only pay the extract/repack cost when something actually changed, or when the
    // archive is missing Dregg2 members entirely (e.g. a freshly-seeded dependency-only base).
    let needs_splice = recompiled || !archive_has_dregg2(archive);
    if !needs_splice {
        return;
    }

    if !archive.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: base archive {} is ABSENT — it must hold the ~5600 \
             precompiled mathlib/batteries/aesop dependency objects, which are EXPENSIVE to \
             regenerate. Run `./scripts/bootstrap.sh` from the repo root: it checks the toolchain \
             + mathlib pin, lake-builds the executor, seeds this archive once, and verifies the \
             link (afterwards plain `cargo build` keeps it fresh automatically). Building \
             marshal-only for now.",
            archive.display()
        );
        return;
    }

    if let Err(e) = splice_objects(archive, &obj_dir, out_dir) {
        println!(
            "cargo:warning=dregg-lean-ffi: archive splice failed ({e}) — the archive was left \
             unchanged; a previous-but-consistent build will be linked."
        );
        return;
    }

    // (4) Closure-completion. The freshly-built Dregg2 objects may import NEW dependency modules
    // (e.g. a `Mathlib.Order.Extension.Linear` that a concurrent edit just added) whose initializer
    // objects are NOT in the frozen base archive's dependency closure. Splicing in only the Dregg2
    // objects would then leave a dangling `_initialize_<dep>` undefined symbol and the FINAL Rust
    // link fails. So we close the archive: detect undefined `_initialize_*` symbols, compile the
    // matching `.c` from the Lean source/dependency IR trees, splice them in, and repeat until the
    // archive is self-contained (or no resolvable `.c` remains — which we surface loudly).
    complete_initializer_closure(meta, sysroot, archive, out_dir);

    // (5) Reachability GC. Closure-completion makes the archive self-LINKING, but the base still
    // carries every dependency object it was ever seeded with — including the mathlib CategoryTheory/
    // Tactic objects the import-trimmed FFI closure no longer references. Drop every member NOT
    // reachable, by symbol, from the `dregg_*` exports. This is the durable payoff of the import-graph
    // split: without it the next splice would re-bloat the archive back to its seeded size.
    //
    // ESCAPE HATCH (`DREGG_LEAN_FFI_NO_ARCHIVE_GC=1`): the GC's symbol-reachability BFS chases only
    // UNDEFINED-symbol edges, so if the closure-completion pass (step 4) seeded an archive whose
    // dependency members reference mathlib FUNCTION symbols that no kept member leaves UNDEFINED (e.g.
    // after a hand re-seed of the FULL dependency closure), the GC can drop the very mathlib members
    // those functions need — leaving `_lp_mathlib_*` unresolved at the final Rust link. When a FULL
    // archive was just restored out-of-band, set this to keep EVERY member (correct, larger) rather
    // than risk the destructive prune. Off by default (the GC stays the steady-state size payoff).
    if std::env::var("DREGG_LEAN_FFI_NO_ARCHIVE_GC").as_deref() == Ok("1") {
        println!(
            "cargo:warning=dregg-lean-ffi: DREGG_LEAN_FFI_NO_ARCHIVE_GC=1 — skipping archive \
             reachability GC, keeping every member (full self-linking archive)."
        );
    } else {
        gc_unreachable_members(archive, out_dir);
    }
}

/// Discover every `.lake/build/ir` directory that can supply a `.c` for the dependency closure:
/// the project's own IR, each git-package IR (`.lake/packages/*/.lake/build/ir`), and each
/// `type:path` dependency's IR (its `dir` is recorded in `lake-manifest.json`; we scan the manifest
/// text for `"dir": "..."` rather than pull a JSON crate into build-deps).
fn discover_ir_roots(meta: &Path) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    let project_ir = meta.join(".lake/build/ir");
    if project_ir.is_dir() {
        roots.push(project_ir);
    }
    let pkgs = meta.join(".lake/packages");
    if let Ok(entries) = std::fs::read_dir(&pkgs) {
        for entry in entries.flatten() {
            let ir = entry.path().join(".lake/build/ir");
            if ir.is_dir() {
                roots.push(ir);
            }
        }
    }
    // `type:path` deps (e.g. a local mathlib checkout): pull their `dir` from the manifest.
    if let Ok(text) = std::fs::read_to_string(meta.join("lake-manifest.json")) {
        for raw in text.split("\"dir\":") {
            // The value is the first quoted string after the key.
            if let Some(start) = raw.find('"') {
                if let Some(end) = raw[start + 1..].find('"') {
                    let dir = &raw[start + 1..start + 1 + end];
                    let p = meta.join(dir).join(".lake/build/ir");
                    if p.is_dir() && !roots.iter().any(|r| r == &p) {
                        roots.push(p);
                    }
                }
            }
        }
    }
    roots
}

/// Lean's C-symbol mangling of a module path: each path component has its INTERNAL underscores
/// doubled (`_`→`__`), then the components are joined with a single `_`. So `A/B/CommMon_.c` →
/// `A_B_CommMon__` — which is exactly the `<flat>` that appears in `_initialize_<lib>_<flat>`. This
/// is what lets the resolver match modules whose name itself contains `_` (e.g. mathlib's `CommMon_`,
/// `Mon_`), which a naive `/`→`_` flatten would get wrong (one `_` instead of two).
fn lean_mangle_relpath(rel: &Path) -> String {
    rel.with_extension("")
        .components()
        .map(|comp| comp.as_os_str().to_string_lossy().replace('_', "__"))
        .collect::<Vec<_>>()
        .join("_")
}

/// Index every `.c` under the IR roots by its Lean-mangled module name (see `lean_mangle_relpath`,
/// e.g. `Mathlib/Order/Extension/Linear.c` → `Mathlib_Order_Extension_Linear`). An undefined
/// `_initialize_<lib>_<flat>` symbol then resolves by stripping the `_initialize_` prefix and
/// matching some suffix of the remainder against this index (the leading `<lib>` token is dropped).
fn build_cfile_index(roots: &[PathBuf]) -> std::collections::HashMap<String, PathBuf> {
    let mut index = std::collections::HashMap::new();
    for root in roots {
        let mut files = Vec::new();
        collect_files(root, &mut files);
        for c in files {
            if c.extension().map(|e| e == "c").unwrap_or(false) {
                if let Ok(rel) = c.strip_prefix(root) {
                    let flat = lean_mangle_relpath(rel);
                    // First writer wins; module names are unique across roots in practice.
                    index.entry(flat).or_insert(c);
                }
            }
        }
    }
    index
}

/// The Lean module initializers that are UNDEFINED in the archive AS A WHOLE: referenced (`U`) by
/// some member but DEFINED (`T`) by NO member. (`nm -u` is unreliable on archives — it lists symbols
/// undefined in individual members even when another member defines them — so we run full `nm` once
/// and compute the U-minus-T set ourselves.) These are the genuine dangling dependency edges the
/// final Rust link would fail on; closure-completion must supply each one's defining object.
fn undefined_initializers(archive: &Path) -> Vec<String> {
    let Ok(out) = Command::new(nm_tool()).arg(archive).output() else {
        return Vec::new();
    };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut defined = std::collections::HashSet::new();
    let mut referenced = std::collections::HashSet::new();
    for line in text.lines() {
        // `nm` archive symbol lines come in two shapes:
        //   "                 U _sym"   (undefined: type letter, then symbol)
        //   "0000000000001234 T _sym"   (defined: address, type letter, symbol)
        // Other lines (blank, "archive.a:", "obj.o:") have no type+symbol and are skipped.
        let toks: Vec<&str> = line.split_whitespace().collect();
        let (ty, sym) = match toks.as_slice() {
            [ty, sym] if ty.len() == 1 => (*ty, *sym), // undefined / no-address
            [_addr, ty, sym] if ty.len() == 1 => (*ty, *sym), // defined / with-address
            _ => continue,
        };
        let name = sym.trim_start_matches('_');
        if let Some(rest) = name.strip_prefix("initialize_") {
            // The toolchain stdlib initializers (Init/Std/Lean/Lake) are supplied by the sysroot
            // static libs the FINAL Rust link pulls in (rustc-link-lib=static={Init,Std,Lean,Lake});
            // they have no `.c` in the project/dependency IR and are NOT ours to splice. Skip them so
            // closure-completion chases only genuinely-missing in-closure modules.
            let toolchain = ["Init", "Std", "Lean", "Lake"]
                .iter()
                .any(|lib| rest == *lib || rest.starts_with(&format!("{lib}_")));
            if toolchain {
                continue;
            }
            if ty == "U" {
                referenced.insert(name.to_string());
            } else {
                defined.insert(name.to_string());
            }
        }
    }
    let mut missing: Vec<String> = referenced.difference(&defined).cloned().collect();
    missing.sort();
    missing
}

/// Map a bare initializer symbol (`initialize_<lib>_<flat>`) to its source `.c` via the index. The
/// `<lib>` token is a single library name (no internal-underscore doubling); we strip `initialize_`,
/// then strip a KNOWN library token + `_`, leaving exactly the Lean-mangled `<flat>` index key. This
/// is unambiguous (vs suffix-guessing, which breaks on `__`-mangled names like `CommMon__`). We try
/// the known tokens longest-first so e.g. `LeanSearchClient` is preferred over a shorter prefix.
fn resolve_initializer_cfile<'a>(
    sym: &str,
    index: &'a std::collections::HashMap<String, PathBuf>,
) -> Option<(String, &'a PathBuf)> {
    let rest = sym.strip_prefix("initialize_")?;
    // Library tokens that prefix a module initializer (the project libs + every dependency package).
    // `Init`/`Std`/`Lean`/`Lake` are filtered out earlier (sysroot-provided), so they need not appear.
    let mut libs = [
        "Dregg2",
        "Metatheory",
        "mathlib",
        "aesop",
        "batteries",
        "importGraph",
        "LeanSearchClient",
        "plausible",
        "proofwidgets",
        "Qq",
        "Cli",
    ];
    libs.sort_by_key(|l| std::cmp::Reverse(l.len()));
    for lib in libs {
        if let Some(flat) = rest.strip_prefix(lib).and_then(|r| r.strip_prefix('_')) {
            if let Some(cfile) = index.get(flat) {
                return Some((flat.to_string(), cfile));
            }
        }
    }
    None
}

/// Iteratively add the dependency-closure objects the freshly-spliced Dregg2 objects need, until the
/// archive has no resolvable undefined `_initialize_*` edge left. Each pass compiles the missing
/// `.c` (cached by flattened name under OUT_DIR) and splices them in; new objects can introduce
/// further deps, hence the loop. Bounded to avoid runaway; unresolved symbols are surfaced loudly.
fn complete_initializer_closure(meta: &Path, sysroot: &Path, archive: &Path, out_dir: &Path) {
    let inc = sysroot.join("include");
    let dep_dir = out_dir.join("dregg2_closure_deps");
    if std::fs::create_dir_all(&dep_dir).is_err() {
        return;
    }
    let roots = discover_ir_roots(meta);
    let index = build_cfile_index(&roots);

    for pass in 0..16 {
        let undefined = undefined_initializers(archive);
        if undefined.is_empty() {
            return;
        }
        // Resolve as many as we can to source `.c`; compile those not already cached.
        let mut to_add: Vec<(String, PathBuf)> = Vec::new(); // (objname, objpath)
        let mut unresolved = Vec::new();
        for sym in &undefined {
            match resolve_initializer_cfile(sym, &index) {
                Some((flat, cfile)) => {
                    let obj = dep_dir.join(format!("{flat}.o"));
                    if newer_than(cfile, &obj) {
                        // `-fPIC` for the same shared-link-compatibility reason as the splice
                        // compile above (one archive, both link modes).
                        let status = Command::new("lake")
                            .args(["env", "leanc", "-c", "-fPIC", "-I"])
                            .arg(&inc)
                            .arg(cfile)
                            .arg("-o")
                            .arg(&obj)
                            .current_dir(meta)
                            .status();
                        if !matches!(status, Ok(s) if s.success()) {
                            let _ = std::fs::remove_file(&obj);
                            println!(
                                "cargo:warning=dregg-lean-ffi: closure leanc failed on {} (dep of \
                                 {sym})",
                                cfile.display()
                            );
                            continue;
                        }
                    }
                    to_add.push((format!("{flat}.o"), obj));
                }
                None => unresolved.push(sym.clone()),
            }
        }

        if to_add.is_empty() {
            if !unresolved.is_empty() {
                println!(
                    "cargo:warning=dregg-lean-ffi: {} undefined initializer(s) could not be \
                     resolved to a `.c` in the IR trees (e.g. {}); the archive may not self-link. \
                     Re-seed the closure (scripts/seed-dregg2-closure.sh) if the dependency set \
                     changed substantially.",
                    unresolved.len(),
                    unresolved.first().map(|s| s.as_str()).unwrap_or("?")
                );
            }
            return;
        }

        if let Err(e) = add_objects_to_archive(archive, &to_add, out_dir) {
            println!("cargo:warning=dregg-lean-ffi: closure splice failed on pass {pass} ({e}).");
            return;
        }
        println!(
            "cargo:warning=dregg-lean-ffi: closure pass {pass}: added {} dependency object(s).",
            to_add.len()
        );
    }
    println!(
        "cargo:warning=dregg-lean-ffi: closure completion hit the 16-pass bound — archive may \
         still have undefined initializers. Consider re-seeding the closure."
    );
}

/// **Archive reachability GC — the import-graph-trim payoff made durable.**
///
/// After the splice + closure-completion the archive self-links, but it still carries every
/// dependency object the BASE archive was ever seeded with — including the thousands of mathlib
/// `CategoryTheory`/`Tactic` objects that the (now import-trimmed) FFI closure no longer references.
/// Lean runs an `initialize_` per ARCHIVED module at boot, so those dead members are not just dead
/// weight — they inflate the linked binary and the wasm executor. `-Oz`/`--gc-sections` cannot strip
/// them (each module's initializer is reachable from its own object's ctor), so we garbage-collect at
/// the ARCHIVE level: keep only members reachable, by symbol, from the `dregg_*` FFI exports.
///
/// Reachability is exact and conservative: a member is kept iff it is the export-defining root, or it
/// defines a symbol that some kept member leaves undefined (`U`). Toolchain-supplied symbols (resolved
/// by the final Rust link against the sysroot `Init`/`Std`/`Lean`/`Lake` static libs) need no archive
/// member, so members that ONLY serve them drop out. If `nm` is unavailable or the computed reachable
/// set looks implausibly small (a parse failure), we SKIP the GC and keep the (correct, larger) archive
/// — never risk a broken link to save bytes.
fn gc_unreachable_members(archive: &Path, out_dir: &Path) {
    let Ok(out) = Command::new(nm_tool()).arg("-A").arg(archive).output() else {
        return;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    use std::collections::{HashMap, HashSet};
    // member -> (defined syms, undefined syms);  symbol -> members defining it.
    let mut undef: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sym_def_in: HashMap<String, HashSet<String>> = HashMap::new();
    let mut members: HashSet<String> = HashSet::new();
    let mut roots: HashSet<String> = HashSet::new();
    for line in text.lines() {
        // `nm -A` location-prefixed forms (see `members_defining_project_initializers`):
        //   macOS/llvm: `<archive>:<member.o>: <addr> T _sym`  /  `<archive>:<member.o>:    U _sym`
        //   GNU:        `<archive>[<member.o>]: <addr> T _sym`
        let Some((prefix, rest)) = line.split_once(": ") else {
            continue;
        };
        let prefix = prefix.trim_end_matches(']');
        let member = prefix.rsplit(['/', ':', '[']).next().unwrap_or(prefix);
        if !member.ends_with(".o") {
            continue;
        }
        let toks: Vec<&str> = rest.split_whitespace().collect();
        let (ty, sym) = match toks.as_slice() {
            [ty, sym] if ty.len() == 1 => (*ty, *sym),
            [_addr, ty, sym] if ty.len() == 1 => (*ty, *sym),
            _ => continue,
        };
        members.insert(member.to_string());
        if ty == "U" || ty == "u" {
            undef
                .entry(member.to_string())
                .or_default()
                .insert(sym.to_string());
        } else {
            sym_def_in
                .entry(sym.to_string())
                .or_default()
                .insert(member.to_string());
            // Root: any member defining a `_dregg_*` FFI export (the C-ABI entry points).
            if sym.trim_start_matches('_').starts_with("dregg_") {
                roots.insert(member.to_string());
            }
        }
    }
    if members.is_empty() || roots.is_empty() {
        // Parse failure or no exports found — do not risk a destructive GC.
        return;
    }
    // BFS: keep a member, then chase each of its undefined symbols to the member(s) defining them.
    let mut reach: HashSet<String> = HashSet::new();
    let mut queue: Vec<String> = roots.iter().cloned().collect();
    while let Some(member) = queue.pop() {
        if !reach.insert(member.clone()) {
            continue;
        }
        if let Some(us) = undef.get(&member) {
            for u in us {
                if let Some(defs) = sym_def_in.get(u) {
                    for dm in defs {
                        if !reach.contains(dm) {
                            queue.push(dm.clone());
                        }
                    }
                }
            }
        }
    }
    let unreachable = members.len().saturating_sub(reach.len());
    if unreachable == 0 {
        return; // already minimal.
    }
    // Sanity floor: the FFI closure genuinely needs hundreds of dependency members; if the reachable
    // set collapsed below a plausible floor the `nm` parse misfired — keep the larger, correct archive.
    if reach.len() < 200 {
        println!(
            "cargo:warning=dregg-lean-ffi: archive GC computed only {} reachable members (< floor) — \
             skipping the prune to avoid a destructive parse error.",
            reach.len()
        );
        return;
    }
    // Repack keeping only reachable members. Extract to scratch, delete the unreachable, `ar rcs`.
    let work = out_dir.join("dregg2_gc_work");
    if work.exists() {
        let _ = std::fs::remove_dir_all(&work);
    }
    if std::fs::create_dir_all(&work).is_err() {
        return;
    }
    if !matches!(Command::new(ar_tool()).arg("x").arg(archive).current_dir(&work).status(), Ok(s) if s.success())
    {
        return;
    }
    let mut kept: Vec<String> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&work) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if !name.ends_with(".o") {
                continue;
            }
            if reach.contains(&name) {
                kept.push(name);
            } else {
                let _ = std::fs::remove_file(entry.path());
            }
        }
    }
    if kept.is_empty() {
        return;
    }
    kept.sort();
    let tmp = out_dir.join("libdregg_lean.a.gc");
    let _ = std::fs::remove_file(&tmp);
    if !matches!(
        Command::new(ar_tool()).arg("rcs").arg(&tmp).args(&kept).current_dir(&work).status(),
        Ok(s) if s.success()
    ) {
        return;
    }
    let _ = run_ranlib(&tmp);
    if std::fs::rename(&tmp, archive).is_err() {
        // Cross-device rename fallback: copy.
        if std::fs::copy(&tmp, archive).is_ok() {
            let _ = std::fs::remove_file(&tmp);
        } else {
            return;
        }
    }
    println!(
        "cargo:warning=dregg-lean-ffi: archive GC pruned {unreachable} unreachable dependency \
         object(s) (kept {} reachable from the `dregg_*` exports).",
        kept.len()
    );
}

/// **The PRINCIPLED elaborator / proof-time TRIM (docs/EMBEDDABLE-LEAN-RUNTIME.md §4.2).**
///
/// `gc_unreachable_members` keeps every member reachable by ANY undefined-symbol edge — and the
/// per-module `initialize_*` chain is such an edge. So the executor's import closure drags in the
/// initializer of every TRANSITIVELY-imported module: `Dregg2.Exec.Kernel`'s init alone chains into
/// `initialize_Dregg2_Dregg2_Tactics` (→ `initialize_Lean`, the whole elaborator) AND the mathlib
/// `Tactic.Ring` / `Algebra.BigOperators` inits, which in turn chain across ~2600 mathlib members.
/// None of that proof-time code is CALLED by the executor's compute path (`Exec.recKExec` /
/// `execFullForestG`) — it enters ONLY through the init chain. The measured shape: the executor's
/// true runtime-FUNCTION closure is ~960 members / ~67 MB; the init-chain inflates the kept archive
/// to ~3000 members / ~138 MB (the elaborator + the proof-time mathlib/aesop).
///
/// This pass severs the init-chain edge at the SHAPE of the closure. It computes the
/// runtime-function/data reachable set from the `dregg_*` exports (following EVERY edge EXCEPT the
/// `initialize_*` ones, which are the boundary), keeps exactly those members in a separate trimmed
/// archive, and supplies a boundary NO-OP for each runtime-DEAD module initializer the kept members'
/// own init-chains still reference (the same mechanism the seL4 lane proved with `init-stubs.c` —
/// generalized from the single `Dregg2.Tactics` leaf to the whole runtime-dead frontier). The result
/// is a dead-stripped static embed of the VERIFIED executor at a fraction of the size, with the
/// elaborator/Mathlib never init-pulled.
///
/// Soundness: a module is dropped ONLY when no live member references any of its function/data
/// symbols — i.e. the executor never calls into it. Its initializer (which only built proof-time
/// constants) is replaced by an idempotent no-op so the live init-chain still links. The verified
/// `def`s and their proofs are untouched (proofs build in the full metatheory; this trims the RUNTIME
/// embed only). The kernel probe (`embeddable_runtime_probe`) drives a real transfer through the
/// trimmed archive as the empirical safety check. OPT-IN (`DREGG_LEAN_FFI_RUNTIME_TRIM=1`) and written
/// to a SEPARATE archive so the default verified link (node / dregg-turn) is byte-for-byte unchanged.
///
/// Returns `Some(stub_c_path)` when the trim ran — the caller compiles that stub into the whole-archive
/// shim and links `dregg_lean_trim` instead of `dregg_lean`. Returns `None` (fall back to the full
/// archive) on any parse failure / implausibly-small live set / no-members-dead.
fn runtime_dead_init_trim(
    full_archive: &Path,
    trim_archive: &Path,
    out_dir: &Path,
) -> Option<PathBuf> {
    use std::collections::{HashMap, HashSet};
    let out = Command::new(nm_tool())
        .arg("-A")
        .arg(full_archive)
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    // member -> undefined NON-init syms / undefined init syms;  sym -> members defining it.
    let mut undef_func: HashMap<String, HashSet<String>> = HashMap::new();
    let mut undef_init: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sym_def_in: HashMap<String, HashSet<String>> = HashMap::new();
    let mut members: HashSet<String> = HashSet::new();
    let mut roots: HashSet<String> = HashSet::new();
    for line in text.lines() {
        let Some((prefix, rest)) = line.split_once(": ") else {
            continue;
        };
        let prefix = prefix.trim_end_matches(']');
        let member = prefix.rsplit(['/', ':', '[']).next().unwrap_or(prefix);
        if !member.ends_with(".o") {
            continue;
        }
        let toks: Vec<&str> = rest.split_whitespace().collect();
        let (ty, sym) = match toks.as_slice() {
            [ty, sym] if ty.len() == 1 => (*ty, *sym),
            [_addr, ty, sym] if ty.len() == 1 => (*ty, *sym),
            _ => continue,
        };
        members.insert(member.to_string());
        let bare = sym.trim_start_matches('_');
        let is_init = bare.starts_with("initialize_");
        if ty == "U" || ty == "u" {
            if is_init {
                undef_init
                    .entry(member.to_string())
                    .or_default()
                    .insert(sym.to_string());
            } else {
                undef_func
                    .entry(member.to_string())
                    .or_default()
                    .insert(sym.to_string());
            }
        } else {
            sym_def_in
                .entry(sym.to_string())
                .or_default()
                .insert(member.to_string());
            if bare.starts_with("dregg_") {
                roots.insert(member.to_string());
            }
        }
    }
    if members.is_empty() || roots.is_empty() {
        return None;
    }

    // RUNTIME-FUNCTION reachability: chase ONLY non-init edges. A module reached purely through an
    // `initialize_*` chain (never by a call/data reference) is runtime-dead and excluded.
    let mut live: HashSet<String> = HashSet::new();
    let mut queue: Vec<String> = roots.iter().cloned().collect();
    while let Some(member) = queue.pop() {
        if !live.insert(member.clone()) {
            continue;
        }
        if let Some(us) = undef_func.get(&member) {
            for u in us {
                if let Some(defs) = sym_def_in.get(u) {
                    for dm in defs {
                        if !live.contains(dm) {
                            queue.push(dm.clone());
                        }
                    }
                }
            }
        }
    }
    // Plausibility floor (mirrors gc_unreachable_members): a misfired parse must not silently
    // produce a tiny broken archive. And if nothing is dead the trim is a no-op — fall back.
    if live.len() < 200 || live.len() >= members.len() {
        return None;
    }

    // The dangling init edges AFTER the trim: an `initialize_*` referenced by a KEPT member but
    // defined only by a DROPPED member needs a boundary no-op so the kept init-chain links.
    // Toolchain inits (Init/Std/Lean/Lake) come from the sysroot static libs the final link pulls,
    // so never no-op those — if a live member genuinely references `initialize_Lean`, let the real
    // (sysroot) init run rather than silently skip it.
    let is_toolchain = |bare: &str| -> bool {
        match bare.strip_prefix("initialize_") {
            Some(rest) => ["Init", "Std", "Lean", "Lake"]
                .iter()
                .any(|lib| rest == *lib || rest.starts_with(&format!("{lib}_"))),
            None => false,
        }
    };
    let mut dangling: HashSet<String> = HashSet::new();
    for m in &live {
        if let Some(us) = undef_init.get(m) {
            for u in us {
                let bare = u.trim_start_matches('_').to_string();
                if is_toolchain(&bare) {
                    continue;
                }
                let defined_by_kept = sym_def_in
                    .get(u)
                    .map(|d| d.iter().any(|dm| live.contains(dm)))
                    .unwrap_or(false);
                if defined_by_kept {
                    continue;
                }
                dangling.insert(bare);
            }
        }
    }

    // Repack the trimmed archive: extract the full archive into scratch, keep only live members.
    let work = out_dir.join("dregg2_runtime_trim_work");
    let _ = std::fs::remove_dir_all(&work);
    std::fs::create_dir_all(&work).ok()?;
    if !matches!(Command::new(ar_tool()).arg("x").arg(full_archive).current_dir(&work).status(), Ok(s) if s.success())
    {
        return None;
    }
    let mut kept: Vec<String> = Vec::new();
    if let Ok(entries) = std::fs::read_dir(&work) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            if !name.ends_with(".o") {
                continue;
            }
            if live.contains(&name) {
                kept.push(name);
            } else {
                let _ = std::fs::remove_file(entry.path());
            }
        }
    }
    if kept.is_empty() {
        return None;
    }
    kept.sort();
    let _ = std::fs::remove_file(trim_archive);
    if !matches!(
        Command::new(ar_tool()).arg("rcs").arg(trim_archive).args(&kept).current_dir(&work).status(),
        Ok(s) if s.success()
    ) {
        return None;
    }
    let _ = run_ranlib(trim_archive);
    let _ = std::fs::remove_dir_all(&work);

    // Generate the boundary no-op stub for the runtime-dead module inits the kept chain references.
    let stub = out_dir.join("runtime_trim_init_stubs.c");
    let mut sorted: Vec<&String> = dangling.iter().collect();
    sorted.sort();
    let mut body = String::new();
    body.push_str(
        "/* GENERATED by dregg-lean-ffi/build.rs::runtime_dead_init_trim — the\n\
         * EMBEDDABLE-LEAN-RUNTIME §4.2 principled elaborator/proof-time trim.\n\
         *\n\
         * Boundary no-op initializers for the RUNTIME-DEAD modules (the proof-time tactics, the\n\
         * Lean elaborator, and the mathlib/aesop the verified executor never CALLS) that were\n\
         * dropped from the trimmed archive. The kept (runtime-live) members' own init-chains still\n\
         * reference these symbols; resolving them HERE severs the elaborator/Mathlib init-pull at\n\
         * the closure boundary. Linked +whole-archive, so these win over any archive definition.\n\
         *\n\
         * Init ABI (Lean v4.30.0): lean_object* initialize_X(uint8_t builtin); idempotent. */\n\
         #include <lean/lean.h>\n\
         #define NOOP_INIT(name)                                            \\\n\
           static uint8_t name##_done = 0;                                  \\\n\
           lean_object *name(uint8_t builtin) {                             \\\n\
             (void)builtin;                                                 \\\n\
             if (name##_done) return lean_io_result_mk_ok(lean_box(0));     \\\n\
             name##_done = 1;                                               \\\n\
             return lean_io_result_mk_ok(lean_box(0));                      \\\n\
           }\n",
    );
    for d in &sorted {
        body.push_str(&format!("NOOP_INIT({d})\n"));
    }
    std::fs::write(&stub, body).ok()?;

    println!(
        "cargo:warning=dregg-lean-ffi: RUNTIME TRIM (EMBEDDABLE §4.2) — kept {} runtime-live of {} \
         members (dropped {} runtime-dead: elaborator + proof-time mathlib/aesop), {} boundary init \
         no-ops. Linking libdregg_lean_trim.a.",
        kept.len(),
        members.len(),
        members.len() - kept.len(),
        sorted.len(),
    );
    Some(stub)
}

/// Add (replace) the given objects into the archive, preserving everything else. Like `splice_objects`
/// but for an arbitrary object set (the dependency-closure additions), and incremental — it does NOT
/// re-extract the whole archive; it uses `ar r` to insert/replace members by name, then `ranlib`.
fn add_objects_to_archive(
    archive: &Path,
    objs: &[(String, PathBuf)],
    out_dir: &Path,
) -> std::io::Result<()> {
    // Stage the objects under their archive member names in a scratch dir, then `ar r` them in.
    let stage = out_dir.join("dregg2_closure_stage");
    if stage.exists() {
        std::fs::remove_dir_all(&stage)?;
    }
    std::fs::create_dir_all(&stage)?;
    let mut names = Vec::new();
    for (name, path) in objs {
        std::fs::copy(path, stage.join(name))?;
        names.push(name.clone());
    }
    // `ar r <archive> *.o` inserts or replaces the named members in place (preserving the other
    // ~6100 members). We pass the absolute archive path and run in the stage dir for clean names.
    let r = Command::new(ar_tool())
        .arg("r")
        .arg(archive)
        .args(&names)
        .current_dir(&stage)
        .status()?;
    if !r.success() {
        return Err(std::io::Error::other(format!("`ar r` exited {r}")));
    }
    let _ = run_ranlib(archive);
    let _ = std::fs::remove_dir_all(&stage);
    Ok(())
}

/// Whether the archive already contains any `Dregg2_*.o` member (via `ar t`). Used to force a
/// splice when the base archive is dependency-closure-only.
fn archive_has_dregg2(archive: &Path) -> bool {
    let Ok(out) = Command::new(ar_tool()).arg("t").arg(archive).output() else {
        return false;
    };
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .any(|l| l.trim().starts_with("Dregg2_") && l.trim().ends_with(".o"))
}

/// The set of archive MEMBER names (e.g. `Await.o`, `Dregg2_Spec_Await.o`) that define a project
/// module initializer (`_initialize_Dregg2_*` / `_initialize_Metatheory_*`). Computed with `nm -A`,
/// which prefixes each symbol line with the member location. The prefix format differs by platform:
///   * macOS/llvm-nm: `<archive>:<member.o>: <addr> T <sym>`
///   * GNU/binutils:  `<archive>[<member.o>]: <addr> T <sym>`
///
/// We extract the member by taking the basename of the path segment ending in `.o`, so the splice can
/// purge stale project objects regardless of how they were named when the base archive was seeded.
fn members_defining_project_initializers(archive: &Path) -> std::collections::HashSet<String> {
    let mut members = std::collections::HashSet::new();
    let Ok(out) = Command::new(nm_tool()).arg("-A").arg(archive).output() else {
        return members;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    for line in text.lines() {
        // Only DEFINING (`T`) lines for a project initializer; skip undefined (`U`) references.
        // The C symbol carries a leading `_` on Mach-O (macOS) but NOT on ELF/COFF (Linux,
        // Windows-MinGW), so accept both `T _initialize_*` and `T initialize_*`.
        let is_project_init = |stem: &str| {
            line.contains(&format!("T _{stem}")) || line.contains(&format!("T {stem}"))
        };
        if !(is_project_init("initialize_Dregg2_") || is_project_init("initialize_Metatheory_")) {
            continue;
        }
        // The location prefix is everything up to the first `: ` (space-separated from the address).
        let Some(prefix) = line.split(": ").next() else {
            continue;
        };
        // Strip a trailing `]` (GNU bracket form), then take the basename and keep it iff it's a `.o`.
        let prefix = prefix.trim_end_matches(']');
        let member = prefix.rsplit(['/', ':', '[']).next().unwrap_or(prefix);
        if member.ends_with(".o") {
            members.insert(member.to_string());
        }
    }
    members
}

/// Splice the freshly-built `Dregg2_*.o` into `archive`, preserving every non-project dependency
/// object. Extract → purge stale project members (by defined symbol, see above) → drop in the fresh
/// `Dregg2_*.o` → `ar rcs` + `ranlib`. Works in a scratch dir under `OUT_DIR` (writable, local).
fn splice_objects(archive: &Path, obj_dir: &Path, out_dir: &Path) -> std::io::Result<()> {
    let work = out_dir.join("dregg2_splice_work");
    if work.exists() {
        std::fs::remove_dir_all(&work)?;
    }
    std::fs::create_dir_all(&work)?;

    // Extract the existing archive (all ~6100 members) into the scratch dir.
    let extract = Command::new(ar_tool())
        .arg("x")
        .arg(archive)
        .current_dir(&work)
        .status()?;
    if !extract.success() {
        return Err(std::io::Error::other(format!("`ar x` exited {extract}")));
    }

    // Purge EVERY stale project-module object, by DEFINED SYMBOL not just filename. The base archive
    // was historically seeded with SHORT member names (`Await.o`, `Transfer.o`, …) while our splice
    // uses flattened names (`Dregg2_Spec_Await.o`); a filename-only purge would leave the short-named
    // stale copies behind as DUPLICATE definitions — and, when a concurrent edit renames/deletes a
    // module, those stale copies carry dangling references to the old name (the empirical cause of the
    // `_initialize_…burnAWitness` / `_initialize_Metatheory_Metatheory_Core` link failures). So we
    // drop every extracted member that defines a `_initialize_Dregg2_*` or `_initialize_Metatheory_*`
    // symbol, then re-add ONLY the freshly compiled objects.
    let stale_members = members_defining_project_initializers(archive);
    for entry in std::fs::read_dir(&work)?.flatten() {
        let fname = entry.file_name();
        let name = fname.to_string_lossy();
        let is_flattened_project = (name.starts_with("Dregg2_") || name.starts_with("Metatheory_"))
            && name.ends_with(".o");
        if is_flattened_project || stale_members.contains(name.as_ref()) {
            std::fs::remove_file(entry.path())?;
        }
    }
    let mut dregg2_count = 0usize;
    for entry in std::fs::read_dir(obj_dir)?.flatten() {
        let name = entry.file_name();
        let name_s = name.to_string_lossy();
        if name_s.starts_with("Dregg2_") && name_s.ends_with(".o") {
            std::fs::copy(entry.path(), work.join(&name))?;
            dregg2_count += 1;
        }
    }

    // Repack into a fresh archive next to build.rs, then atomically swap it into place. `ar rcs`
    // over the entire member set (Dregg2 + preserved dependency closure) followed by `ranlib`
    // rebuilds the symbol index. We pass the member list explicitly to keep ordering deterministic.
    let members: Vec<PathBuf> = std::fs::read_dir(&work)?
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().map(|e| e == "o").unwrap_or(false))
        .collect();
    if members.is_empty() {
        return Err(std::io::Error::other(
            "no .o members after extract — refusing to repack",
        ));
    }

    let tmp_archive = out_dir.join("libdregg_lean.a.new");
    let _ = std::fs::remove_file(&tmp_archive);
    // `ar rcs <out> *.o` — build with relative paths from `work` to keep member names clean.
    let rel_members: Vec<String> = members
        .iter()
        .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    let rcs = Command::new(ar_tool())
        .arg("rcs")
        .arg(&tmp_archive)
        .args(&rel_members)
        .current_dir(&work)
        .status()?;
    if !rcs.success() {
        return Err(std::io::Error::other(format!("`ar rcs` exited {rcs}")));
    }
    let ranlib = run_ranlib(&tmp_archive);
    // ranlib is advisory: `ar s`/`rcs` already wrote a symbol table on most toolchains. Only warn.
    if !matches!(ranlib, Ok(s) if s.success()) {
        println!(
            "cargo:warning=dregg-lean-ffi: ranlib on the new archive did not succeed (continuing)."
        );
    }

    std::fs::rename(&tmp_archive, archive)?;
    let _ = std::fs::remove_dir_all(&work);
    println!(
        "cargo:warning=dregg-lean-ffi: spliced {dregg2_count} Dregg2 objects into {} ({} total members).",
        archive.display(),
        rel_members.len()
    );
    Ok(())
}

/// Probe the archive for an exported symbol via `nm`, so the C shim only declares string
/// bridges whose underlying Lean `@[export]` actually exists in THIS archive. A stale
/// archive missing a later export (e.g. `dregg_exec_handler_turn`) would otherwise leave a
/// dangling reference that `-dead_strip` resolves by dropping the WHOLE shim object — taking
/// the forest-auth + init bridges with it. We fail-closed: absent ⇒ the bridge is compiled out.
fn archive_exports(archive: &std::path::Path, symbol: &str) -> bool {
    let Ok(out) = Command::new(nm_tool()).arg(archive).output() else {
        return false;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    // A DEFINED symbol shows in the text section as `T <name>`. The C symbol name is mangled
    // with a leading underscore on Mach-O (macOS) but NOT on ELF (Linux), so accept both
    // ` T _<symbol>` and ` T <symbol>`.
    let mach_o = format!(" T _{symbol}");
    let elf = format!(" T {symbol}");
    text.lines()
        .any(|l| l.trim_end().ends_with(&mach_o) || l.trim_end().ends_with(&elf))
}

/// Whether the SHARED link mode is selected (`DREGG_LEAN_LINK=shared`).
///
/// An ENV VAR, deliberately NOT a cargo feature: features UNIFY across a workspace
/// dependency graph (a cdylib member asking for shared linkage would flip every native
/// crate in the same build), while an env var stays local to the invoking build. The one
/// consumer today is the standalone sdk-py workspace (a pyo3 cdylib), whose
/// `.cargo/config.toml` `[env]` sets it.
///
/// WHY a cdylib cannot use the static mode on ELF: rustc BUNDLES `static=`-linked native
/// libraries into the rlib, and `libleanrt.a`'s mimalloc objects (`static.c.o`:
/// `mi_heap_default` & co.) use local-exec TLS — `R_X86_64_TPOFF32` relocations that the
/// linker rejects under `-shared` (Convergence round 7). The Lean toolchain ships the
/// whole runtime+stdlib built FOR shared use as `libleanshared.{so,dylib}` in
/// `$LEAN_SYSROOT/lib/lean`; shared mode links that instead of the static
/// {leancpp,Init,Std,Lean,leanrt,Lake,gmp,uv} set. Our spliced `libdregg_lean.a` is still
/// linked statically in both modes — it holds ONLY Lean-compiled MODULE objects (Dregg2 +
/// the mathlib/batteries/… dependency closure; never runtime members), all compiled
/// `-fPIC`, so its symbols are disjoint from leanshared's.
fn shared_link_mode() -> bool {
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_LINK");
    match std::env::var("DREGG_LEAN_LINK") {
        Ok(v) if v == "shared" => true,
        Ok(v) if v.is_empty() || v == "static" => false,
        Ok(v) => {
            println!(
                "cargo:warning=dregg-lean-ffi: unknown DREGG_LEAN_LINK={v:?} (expected \
                 `shared` or `static`) — defaulting to the static link."
            );
            false
        }
        Err(_) => false,
    }
}

fn main() {
    println!("cargo::rustc-check-cfg=cfg(lean_lib_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_handler_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_finalize_gate_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_strand_admit_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_distributed_exports_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_decide_refines_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_direct_present)");

    // ── FAIL-LOUD GATE (DREGG_REQUIRE_LEAN) — see docs/BUILD-LEAN-LINKED-NODE.md ─────────────
    // A distribution / CI / validator build REFUSES a silent degrade to the marshal-only shell
    // (`lean_available()==false`, the UN-verified Rust executor). Historically every marshal-only
    // degrade below emitted only a `cargo:warning=…`, which is trivially lost in a release/CI log —
    // so a build whose Lean seed was stale or gitignored could ship as if verified.
    //
    // The gate now has TWO tiers:
    //
    //   * EXPLICIT (`DREGG_REQUIRE_LEAN=1`) — `require_lean`: forces EVERY marshal-only degrade to
    //     a hard build FAILURE, INCLUDING the platform-incapable targets (wasm32 / zkvm /
    //     windows-msvc / no-lean-link). Use it to assert "this build must be a verified node" and
    //     fail loudly if the target can't be one.
    //
    //   * RELEASE-DEFAULT — `require_lean_native`: for a NATIVE, archive-linkable target, a
    //     `--release` (distribution) build defaults the fail-loud gate ON so a release binary can
    //     never SILENTLY ship marshal-only. This covers the archive-absent / sysroot-unresolvable
    //     degrades (the real "ships as verified but isn't" cases). It does NOT fire on the
    //     platform-incapable early return (those targets legitimately can't link Lean; only the
    //     EXPLICIT tier forces them). The opt-out for a deliberately-marshal-only release build
    //     (dev / benchmarks / a non-node crate) is `DREGG_REQUIRE_LEAN=0` (or `false`/`off`).
    //
    // Debug/dev builds keep the historical warn-and-degrade behavior unless `DREGG_REQUIRE_LEAN=1`.
    println!("cargo:rerun-if-env-changed=DREGG_REQUIRE_LEAN");
    println!("cargo:rerun-if-env-changed=PROFILE");
    let require_lean_env = std::env::var("DREGG_REQUIRE_LEAN").ok();
    let require_lean = matches!(
        require_lean_env.as_deref(),
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    );
    let require_lean_off = matches!(
        require_lean_env.as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    );
    // Cargo sets PROFILE to "release" for `--release` (and any release-profile) builds.
    let is_release = std::env::var("PROFILE").as_deref() == Ok("release");
    // Native-target release builds fail loud on a marshal-only degrade unless explicitly opted out.
    let require_lean_native = require_lean || (is_release && !require_lean_off);
    let degrade_guard = |forced: bool, reason: &str| {
        if forced {
            panic!(
                "dregg-lean-ffi: the Lean-required gate is ACTIVE (DREGG_REQUIRE_LEAN=1, or a \
                 --release/distribution build on a native archive-linkable target) but this build \
                 would degrade to MARSHAL-ONLY (lean_available()==false): {reason}. A marshal-only \
                 binary runs the UN-verified Rust executor and must NEVER ship as a verified node. \
                 Fix the cause (usually: install elan+lake and the mathlib pin, and (re)seed a \
                 HEAD-matching dregg-lean-ffi/libdregg_lean.a via ./scripts/bootstrap.sh — the seed \
                 must match the current Lean HEAD or the closure link fails; see \
                 docs/BUILD-LEAN-LINKED-NODE.md), or set DREGG_REQUIRE_LEAN=0 to allow a \
                 deliberately-marshal-only (degraded) build."
            );
        }
    };

    // ── PLATFORM GATE (polarity inversion, docs/FEATURE-HYGIENE.md §Lean): the link is
    // UNCONDITIONAL on native; the ONE opt-out is the `no-lean-link` platform feature, set
    // only by builds whose target cannot link libdregg_lean.a (wasm32, the SP1 zkvm guest,
    // and Windows-MSVC). We also hard-skip on those targets regardless of the feature — a
    // build that forgot to wire `no-lean-link` should degrade to the marshal-only stubs,
    // never attempt a native-archive link. No archive refresh, no shim, no link directives:
    // the crate builds marshal-only and `lean_available()` is false.
    //
    // WINDOWS — TWO DISTINCT TARGETS, only ONE links (measured empirically, docs/desktop-os-
    // research/WINDOWS-PORT.md §lever):
    //
    //   * `x86_64-pc-windows-MSVC` — HARD WALL, hard-skips. The Lean Windows toolchain is the
    //     LLVM-MinGW distribution (`x86_64-w64-windows-gnu`); it ships its runtime+stdlib ONLY
    //     as MinGW `.a` archives of GNU-flavoured `coff-x86-64` objects. MSVC `link.exe`
    //     STRUCTURALLY cannot consume those — every precompiled runtime member (e.g.
    //     `libleanrt.a(object.cpp.obj)`) triggers `LNK1143: no symbol for COMDAT section`
    //     (the GNU-vs-MSVC COMDAT encoding divergence). No MSVC-ABI Lean runtime exists, so an
    //     MSVC native-full build can only be the marshal-only shell. Skip ⇒ `lean_available()==false`.
    //
    //   * `x86_64-pc-windows-GNU` — THE LEVER, proceeds. The MinGW ABI matches the Lean toolchain
    //     exactly: the spliced archive is a GNU `.a` of `coff-x86-64` objects, driven by the LLVM
    //     `llvm-ar`/`llvm-nm`/`leanc` trio (see `ar_tool`/`nm_tool`), and the final link pulls the
    //     Lean MinGW system-lib closure + an ntdll import-lib shim (see `windows_gnu_link_env`).
    //     A trivial Rust-gnu binary statically linking the real Lean runtime LINKS AND RUNS the
    //     embedded `lean_initialize_runtime_module()` under Windows-on-ARM x64 emulation.
    //
    // wasm32 and the SP1 zkvm guest always skip (no native archive at all). The `no-lean-link`
    // platform feature is the explicit opt-out. See docs/FEATURE-HYGIENE.md §Lean.
    let no_lean_link = std::env::var_os("CARGO_FEATURE_NO_LEAN_LINK").is_some();
    let gate_arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let gate_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let gate_env = std::env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    let windows_msvc = gate_os == "windows" && gate_env != "gnu";
    if no_lean_link || gate_arch == "wasm32" || gate_os == "zkvm" || windows_msvc {
        // Platform-incapable targets legitimately cannot link Lean — only the EXPLICIT tier
        // (DREGG_REQUIRE_LEAN=1) forces a failure here, NOT the release-default.
        degrade_guard(
            require_lean,
            &format!(
                "target {gate_arch}/{gate_os} (env {gate_env}) cannot link libdregg_lean.a \
             (no-lean-link feature / wasm32 / zkvm / windows-msvc) — a verified node must be \
             built for a native archive-linkable target"
            ),
        );
        return;
    }

    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR set by cargo"));
    // The git-tracked SEED archive (read-only input; a `cargo build` never writes it).
    let seed_archive = crate_dir.join("libdregg_lean.a");
    // The per-OUT_DIR WORKING archive: where splice / closure-completion / GC happen and
    // what we link against. Per-(crate,feature-set,profile) ⇒ concurrent multi-feature
    // lanes never tear a shared file. See the SWARM-SAFE ARCHIVE note at the top of file.
    let build_archive = out_dir.join("libdregg_lean.a");
    // The SEPARATE trimmed archive (the EMBEDDABLE §4.2 elaborator/proof-time trim). Written ONLY
    // when `DREGG_LEAN_FFI_RUNTIME_TRIM=1`; the default link never touches it, so the verified node /
    // dregg-turn closure is byte-for-byte unchanged.
    let trim_archive = out_dir.join("libdregg_lean_trim.a");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/lean_init.c");
    println!("cargo:rerun-if-changed=src/lean_init_st.cpp");
    // OPT-IN runtime trim. rerun-if-env-changed so toggling it re-runs build.rs (and re-derives the
    // trimmed archive / restores the full link).
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_FFI_RUNTIME_TRIM");
    let runtime_trim_requested = std::env::var("DREGG_LEAN_FFI_RUNTIME_TRIM").as_deref() == Ok("1");

    // Resolve the toolchain + metatheory location up front so we can both (a) refresh the archive
    // from the Lean source when it changed and (b) drive the link below. `lean_sysroot()` honours
    // `DREGG_LEAN_SYSROOT`; `metatheory_dir()` honours `DREGG_METATHEORY_DIR`.
    let sysroot_opt = lean_sysroot();
    let meta_opt = metatheory_dir();

    // ── SEED the per-OUT_DIR working archive from the git-tracked seed (read-only input). This
    // copies the seed into `$OUT_DIR/libdregg_lean.a` once (and re-copies whenever the seed is
    // newer than the working copy, e.g. after an out-of-band re-seed). All splice / closure /
    // GC mutation below targets `build_archive`, never the seed — so concurrent multi-feature
    // lanes never tear the shared file. `cargo:rerun-if-changed` on the seed re-runs build.rs
    // when the seed is re-produced out-of-band, picking up the fresh base.
    println!("cargo:rerun-if-changed={}", seed_archive.display());
    seed_build_archive(&seed_archive, &build_archive);

    // ── PRODUCE / REFRESH the archive from the Lean source (the linchpin). We watch the whole
    // `metatheory/Dregg2` source tree + the toolchain marker; when any of those change, build.rs
    // reruns and `build_dregg2_archive` does the incremental `lake build` → `leanc -c` → `ar`
    // splice INTO THE PER-OUT_DIR WORKING ARCHIVE. A genuine no-op cargo build does NOT rerun
    // build.rs (no watched file changed), so the ~6000-object closure is never needlessly
    // regenerated. The working archive (`build_archive`) is our OWN per-build output; we do not
    // `rerun-if-changed` it (it lives in OUT_DIR and watching it would loop).
    if let Some(meta) = &meta_opt {
        let mut watched = Vec::new();
        collect_files(&meta.join("Dregg2"), &mut watched);
        for f in &watched {
            println!("cargo:rerun-if-changed={}", f.display());
        }
        println!(
            "cargo:rerun-if-changed={}",
            meta.join("lean-toolchain").display()
        );

        match &sysroot_opt {
            Some(sysroot) => {
                build_dregg2_archive(meta, sysroot, &build_archive, &out_dir, &seed_archive)
            }
            None => println!(
                "cargo:warning=dregg-lean-ffi: cannot resolve the Lean sysroot (no \
                 DREGG_LEAN_SYSROOT and `lake env` failed in metatheory/) — skipping the archive \
                 refresh; the existing archive (if any) is used as-is. The two common causes: \
                 (1) elan/lake is not installed or not on PATH; (2) the mathlib LOCAL-PATH \
                 dependency pinned in metatheory/lakefile.toml is missing on this machine. \
                 `./scripts/bootstrap.sh` (repo root) checks both and teaches the exact fix."
            ),
        }
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: metatheory/ not found (set DREGG_METATHEORY_DIR) — \
             cannot refresh libdregg_lean.a from Lean source; using the existing archive if present."
        );
    }

    if !build_archive.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a absent (no git-tracked seed AND no \
             prior per-OUT_DIR working archive) — building MARSHAL-ONLY: lean_available() will be \
             false and the node falls back to the UNVERIFIED Rust executor. To link the verified \
             Lean kernel, run `./scripts/bootstrap.sh` from the repo root (one command: it checks \
             elan + the mathlib pin, lake-builds the executor, seeds the archive once, and \
             verifies the link). Afterwards plain `cargo build` copies the seed into OUT_DIR and \
             keeps its Dregg2 slice fresh automatically."
        );
        // The real "ships as verified but isn't" case on a native target — the release-default
        // tier fails loud here so a distribution binary can never silently be marshal-only.
        degrade_guard(
            require_lean_native,
            "libdregg_lean.a absent — no seed and no prior per-OUT_DIR working archive (run \
             ./scripts/bootstrap.sh to lake-build + seed the Lean archive)",
        );
        return;
    }

    // Resolve the Lean sysroot BEFORE committing to the `lean_lib_present` cfg: linking the
    // archive requires the Lean runtime/stdlib from the toolchain. If we cannot find it, we must
    // NOT advertise `lean_lib_present` (that cfg drives `lean_available()` and the FFI link), or
    // the build would either fail to link or falsely claim the Lean kernel is available.
    let Some(sysroot) = sysroot_opt else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a present but could not resolve the Lean \
             sysroot (no DREGG_LEAN_SYSROOT and `lake env` failed) — building marshal-only. \
             Install elan + the project toolchain (`./scripts/bootstrap.sh` checks everything \
             and teaches the fix), or set DREGG_LEAN_SYSROOT to the toolchain root."
        );
        degrade_guard(
            require_lean_native,
            "the Lean sysroot could not be resolved (no DREGG_LEAN_SYSROOT and `lake env` failed) \
             — install elan + the pinned toolchain so the archive can be linked",
        );
        return;
    };
    let lean_lib = sysroot.join("lib").join("lean");
    let lean_include = sysroot.join("include");

    println!("cargo:rustc-cfg=lean_lib_present");

    // ── THE PRINCIPLED ELABORATOR / PROOF-TIME TRIM (docs/EMBEDDABLE-LEAN-RUNTIME.md §4.2) ──
    // OPT-IN (`DREGG_LEAN_FFI_RUNTIME_TRIM=1`): derive a SEPARATE trimmed archive holding only the
    // executor's runtime-FUNCTION closure (the elaborator + proof-time mathlib/aesop, reachable only
    // via the per-module init-chain, are dropped), plus a boundary no-op stub for the dead inits the
    // kept chain references. Returns the stub path on success; falls back to the full archive on any
    // snag. The DEFAULT (env unset) path skips this entirely — the verified link is unchanged.
    let runtime_trim_stub = if runtime_trim_requested {
        runtime_dead_init_trim(&build_archive, &trim_archive, &out_dir)
    } else {
        None
    };

    // The handler-cutover export is a SECONDARY path; older archives predate it. Only wire its
    // string bridge when the archive actually exports it (otherwise the dangling ref breaks the
    // whole shim under -dead_strip). The forest-auth gate is the load-bearing path and is always
    // present.
    let handler_present = archive_exports(&build_archive, "dregg_exec_handler_turn");
    if handler_present {
        println!("cargo:rustc-cfg=dregg_handler_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_exec_handler_turn` — \
             the handler-cutover bridge is compiled out (forest-auth gate unaffected). \
             Rebuild the archive to enable shadow_exec_handler_turn."
        );
    }

    // The verified FINALITY GATE export (`dregg_blocklace_finalize`) lives in
    // `Dregg2.Distributed.FinalityGate`, a module OUTSIDE the FFI module's import closure. The
    // archive splice compiles every `Dregg2/**/*.c` present in the IR tree, so once the module has
    // been `lake build`- t its object is spliced in and this symbol appears. Until then (e.g. a
    // stale archive) we compile the bridge out and the node falls back to the un-gated path.
    let finalize_gate_present = archive_exports(&build_archive, "dregg_blocklace_finalize");
    if finalize_gate_present {
        println!("cargo:rustc-cfg=dregg_finalize_gate_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_blocklace_finalize` — \
             the verified finality-gate bridge is compiled out (executor gate unaffected). \
             Rebuild the archive (it splices Dregg2.Distributed.FinalityGate) to enable the gate."
        );
    }

    // The verified STRAND-ADMISSION GATE export (`dregg_strand_admit`) lives in
    // `Dregg2.Distributed.StrandAdmission`, also OUTSIDE the FFI module's import closure. Same
    // splice/probe discipline as the finality gate: once the module is `lake build`-t its object is
    // spliced in (the self-linking closure follows the C shim's `initialize_…_StrandAdmission` ref)
    // and this symbol appears; until then we compile the bridge out and the federation falls back to
    // the Rust admission gate.
    let strand_admit_present = archive_exports(&build_archive, "dregg_strand_admit");
    if strand_admit_present {
        println!("cargo:rustc-cfg=dregg_strand_admit_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_strand_admit` — \
             the verified strand-admission bridge is compiled out (federation falls back to the \
             Rust gate). Rebuild the archive (it splices Dregg2.Distributed.StrandAdmission) to \
             enable the Lean-backed F-4 admission gate."
        );
    }

    // The verified CapTP+coord DISTRIBUTED-EXPORTS module (`dregg_captp_validate_handoff` and its five
    // siblings) lives in `Dregg2.Exec.DistributedExports`, also OUTSIDE the FFI module's import
    // closure. Same splice/probe discipline: once the module is `lake build`-t its object is spliced
    // in (the self-linking closure follows the C shim's `initialize_…_DistributedExports` ref) and the
    // symbols appear; until then we compile the six bridges out and the captp/coord runtime falls back
    // to its native Rust gates. We probe a single representative export — they are all defined in the
    // same module, so they are present/absent together.
    let distributed_exports_present =
        archive_exports(&build_archive, "dregg_captp_validate_handoff");
    if distributed_exports_present {
        println!("cargo:rustc-cfg=dregg_distributed_exports_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_captp_validate_handoff` — \
             the verified CapTP+coord decision bridges are compiled out (captp/coord fall back to \
             native Rust gates). Rebuild the archive (it splices Dregg2.Exec.DistributedExports) to \
             enable the Lean-backed handoff / GC-drop / pipeline / 2PC / causal / shared-budget gates."
        );
    }

    // The verified FLOW-REFINEMENT DECISION export (`dregg_decide_refines`) lives in
    // `Dregg2.Deos.FlowRefine`, also OUTSIDE the FFI module's import closure. Same splice/probe
    // discipline: once the module is `lake build`-t (it is in `lake_targets` above) its object is
    // spliced in (the self-linking closure follows the C shim's `initialize_…_FlowRefine` ref) and
    // the symbol appears; until then the `dregg_decide_refines_str` bridge is compiled out and
    // `dregg-deploy/src/refine.rs` falls back to its in-process σ-free mirror of `decideRefines`.
    let decide_refines_present = archive_exports(&build_archive, "dregg_decide_refines");
    if decide_refines_present {
        println!("cargo:rustc-cfg=dregg_decide_refines_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_decide_refines` — \
             the verified flow-refinement decision bridge is compiled out (dregg-deploy's refine \
             gate falls back to its in-process mirror). Rebuild the archive (it splices \
             Dregg2.Deos.FlowRefine) to run the PROVEN decideRefines at the deploy gate."
        );
    }

    // The NO-COPY DIRECT boundary export (`dregg_exec_full_forest_auth_direct`) + its builder/reader
    // family live in `Dregg2.Exec.FFIDirect`. FFIDirect IMPORTS `Dregg2.Exec.FFI` (not the reverse),
    // so its module initializer is OUTSIDE the FFI closure: `dregg_ffi_init` must run
    // `initialize_Dregg2_Dregg2_Exec_FFIDirect` explicitly (gated on DREGG_DIRECT in the C shim).
    // We probe + gate the Rust `extern "C"` block AND the C shim define so a stale archive lacking the
    // export degrades to the JSON path rather than dangling at link time.
    let direct_present = archive_exports(&build_archive, "dregg_exec_full_forest_auth_direct");
    if direct_present {
        println!("cargo:rustc-cfg=dregg_direct_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_exec_full_forest_auth_direct` \
             — the no-copy direct boundary is compiled out (the JSON marshalling path is used). \
             Rebuild the archive (it splices Dregg2.Exec.FFIDirect) to enable the lean_object* path."
        );
    }

    // Compile the C init shim (it uses the `static inline` runtime helpers from
    // <lean/lean.h>, which have no linkable symbol and so must be used from C).
    //
    // We suppress cc's automatic `rustc-link-lib` directive (`cargo_metadata(false)`)
    // and emit our own `+whole-archive` directive below. Reason: the final link runs
    // under `-Wl,-dead_strip` with `-nodefaultlibs`, and on macOS ld64 the shim's
    // single object is otherwise dead-stripped before the linker has recorded the
    // binary's undefined references to `dregg_ffi_init` / `dregg_exec_full_forest_auth_str`
    // (an archive-member-ordering hazard). Forcing the whole archive in guarantees the
    // bridge symbols are present regardless of link order — the empirical fix for the
    // `marshal_roundtrip` / `full_turn_differential` link failures.
    let mut shim = cc::Build::new();
    shim.file("src/lean_init.c").include(&lean_include);
    // The SINGLE-THREADED / libuv-thread-free init (docs/EMBEDDABLE-LEAN-RUNTIME.md).
    // A C++ TU (it calls the namespaced `lean::initialize_*` runtime initializers
    // directly, skipping `initialize_libuv` so the libuv event-loop thread is never
    // spawned — the pg-Tier-D-embeddable path). Compiled into the SAME shim archive so
    // its `dregg_ffi_init_st` symbol propagates with the C bridges; purely additive (the
    // default `dregg_ffi_init` path is unchanged). `.cpp` ⇒ cc drives the C++ compiler.
    shim.file("src/lean_init_st.cpp");
    // The runtime-trim boundary no-op initializers (only present under DREGG_LEAN_FFI_RUNTIME_TRIM=1):
    // resolves the runtime-dead module inits the trimmed archive's kept chain still references, so the
    // elaborator/Mathlib init-pull is severed at the closure boundary. Compiled into the SAME
    // whole-archive shim so the no-ops win over any archive definition.
    if let Some(stub) = &runtime_trim_stub {
        shim.file(stub);
    }
    // SHARED link mode (the cdylib path, `DREGG_LEAN_LINK=shared`): `libleanshared`
    // exports the C-ABI `lean_initialize_runtime_module` but HIDES the individual
    // `lean::initialize_*` C++ symbols `dregg_ffi_init_st` calls. Supplying them from
    // a static `libleanrt.a` copy creates a fatal SPLIT-BRAIN runtime (two copies of
    // the runtime's global state — the in-backend SIGSEGV). So under shared linkage
    // the ST init MUST route through the single exported runtime: `DREGG_LEAN_SHARED`
    // makes `lean_init_st.cpp` call `lean_initialize_runtime_module` (one runtime
    // copy). NOTE: that exported init pulls libuv, so the shared-mode `dregg_ffi_init_st`
    // is NOT libuv-thread-free — the libuv-free property holds only on the STATIC link
    // (the host probe + the standalone node). See `docs/EMBEDDABLE-LEAN-RUNTIME.md` §5.
    let shared = shared_link_mode();
    if shared {
        shim.define("DREGG_LEAN_SHARED", None);
    }
    if handler_present {
        shim.define("DREGG_HANDLER_TURN", None);
    }
    if finalize_gate_present {
        shim.define("DREGG_FINALIZE_GATE", None);
    }
    if strand_admit_present {
        shim.define("DREGG_STRAND_ADMIT", None);
    }
    if distributed_exports_present {
        shim.define("DREGG_DISTRIBUTED_EXPORTS", None);
    }
    if decide_refines_present {
        shim.define("DREGG_DECIDE_REFINES", None);
    }
    if direct_present {
        shim.define("DREGG_DIRECT", None);
    }
    // We drive the link with `rustc-link-lib` / `rustc-link-search` directives, NOT
    // `rustc-link-arg`. WHY: with the package's `links = "dregg_lean"` key, build-script
    // `rustc-link-lib` / `rustc-link-search` directives PROPAGATE to every DOWNSTREAM binary
    // (the `dregg-turn` lean-shadow tests, the node, …) — whereas `rustc-link-arg` is local
    // to this crate's own targets only. The cross-crate propagation is exactly what the
    // shadow harness needs to resolve `dregg_ffi_init` / `dregg_exec_full_forest_auth_str`.
    //
    // The shim is linked `+whole-archive` so its single bridge object survives the final
    // `-Wl,-dead_strip` regardless of archive-member ordering (the empirical fix for the
    // earlier `Undefined symbols` link failures). `+whole-archive` is a link-LIB modifier,
    // so it propagates too.
    shim.cargo_metadata(false);
    shim.compile("dregg_ffi_shim");
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let shim_archive = out_dir.join("libdregg_ffi_shim.a");

    // We drive the link with `rustc-link-lib` / `rustc-link-search` directives ONLY. With the
    // package's `links = "dregg_lean"` key these PROPAGATE to EVERY target that links this
    // crate's rlib — the `dregg-turn` lean-shadow tests + node (downstream) AND this crate's
    // own bins/tests (which `use dregg_lean_ffi` and so link the rlib). Emitting `rustc-link-arg`
    // in ADDITION would DOUBLE-link the shim for the FFI-crate-internal consumers (they'd see
    // the shim both via the propagated lib AND the arg) → "duplicate symbol" errors. So: one
    // mechanism. The standalone differential bins each carry `use dregg_lean_ffi as _;` to force
    // the rlib edge so they inherit these propagated directives.
    //
    // The shim is linked `+whole-archive` so its single bridge object survives the final
    // `-Wl,-dead_strip` regardless of archive-member ordering (the empirical link-failure fix).
    let _ = shim_archive;
    // BOTH the shim AND the spliced Lean archive resolve from `OUT_DIR` (the per-build working
    // copy of `libdregg_lean.a`, seeded from the git-tracked seed and then spliced/GC'd HERE).
    // We deliberately do NOT add `crate_dir` to the search path: pointing the linker at the
    // git-tracked seed would (a) reintroduce the wrong-feature-set race this split closes and
    // (b) link a non-GC'd (full-closure) archive. One search root for our static libs: OUT_DIR.
    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static:+whole-archive=dregg_ffi_shim");
    // Under the runtime trim, link the SEPARATE trimmed archive (`libdregg_lean_trim.a`); otherwise
    // the full verified closure (`libdregg_lean.a`). The trimmed archive holds the same verified
    // executor objects (the `dregg_*` exports + their runtime-function closure), only without the
    // proof-time elaborator/Mathlib members.
    if runtime_trim_stub.is_some() {
        println!("cargo:rustc-link-lib=static=dregg_lean_trim");
    } else {
        println!("cargo:rustc-link-lib=static=dregg_lean");
    }
    println!("cargo:rustc-link-search=native={}", lean_lib.display());
    println!(
        "cargo:rustc-link-search=native={}",
        sysroot.join("lib").display()
    );
    if shared {
        // ── SHARED runtime link (`DREGG_LEAN_LINK=shared`, see `shared_link_mode`) ──
        // The runtime+stdlib come from the toolchain's shared libraries instead of the
        // static archives (whose leanrt/mimalloc members are illegal in a `-shared` ELF
        // link). Link, in leanc's own order, every shared shell the sysroot ships:
        //   * Init_shared / leanshared_1 / leanshared_2 — the symbol-partition shells
        //     (real partitions on Windows; export-empty alongside the full libleanshared
        //     on macOS, where nm shows the whole runtime in libleanshared itself). We
        //     link whichever exist so the set is right on every platform.
        //   * leanshared — the runtime + Init/Std/Lean + leancpp + gmp + uv.
        //   * Lake_shared — Lake lives OUTSIDE leanshared, and the dependency closure
        //     references it (importGraph → `initialize_Lake_Util_Casing`), mirroring the
        //     `static=Lake` line of the static mode.
        // No c++/gmp/uv directives: leanshared bundles gmp+uv and carries its own libc++
        // dependency.
        for name in [
            "Init_shared",
            "leanshared_1",
            "leanshared_2",
            "leanshared",
            "Lake_shared",
        ] {
            let dylib = lean_lib.join(format!("lib{name}.dylib"));
            let so = lean_lib.join(format!("lib{name}.so"));
            if dylib.exists() || so.exists() {
                println!("cargo:rustc-link-lib=dylib={name}");
            }
        }
        // rpath so THIS crate's own bins/tests resolve libleanshared at run time.
        // `rustc-link-arg` does NOT propagate through the `links` key (unlike the
        // link-lib/link-search directives above), so downstream cdylibs — sdk-py — emit
        // their own rpath from their own build.rs.
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
        println!(
            "cargo:rustc-link-arg=-Wl,-rpath,{}",
            sysroot.join("lib").display()
        );
    } else if target_os == "windows" {
        // ── WINDOWS-MinGW (`x86_64-pc-windows-gnu`) STATIC LINK ──────────────────────
        // The Lean LLVM-MinGW toolchain ships its runtime+stdlib AND a near-complete MinGW
        // system-lib sysroot under `$SYSROOT/lib` (sibling to `lib/lean`). The exact lib set
        // below MIRRORS what `leanc -###` itself passes to the linker for a Windows link
        // (lean modules + runtime + the `gmp/uv/icu/...` deps + the Win32 import libs + the
        // clang_rt builtins). `windows_gnu_link_env` has already put both lib dirs + the
        // `clang/19/lib/windows` builtins dir on the search path and generated the ntdll/gcc
        // shim. Proven end-to-end: a Rust-gnu binary linking exactly this set statically links
        // the real Lean runtime and runs `lean_initialize_runtime_module()` under x64 emulation.
        windows_gnu_link_env(&sysroot);
        // Lean modules + runtime core (leancpp before Lean/Std/Init before leanrt, matching
        // leanc's order — the C++ elaborator core resolves against later-listed members).
        for name in [
            "leancpp",
            "Lean",
            "Std",
            "Init",
            "leanrt",
            "Lake",
            "leanmanifest",
        ] {
            println!("cargo:rustc-link-lib=static={name}");
        }
        // Lean's bundled LLVM libc++ (the `std::__1::` ABI the runtime is compiled against),
        // its math/number deps, then the Win32 import libs the runtime + libuv reference.
        for name in [
            "c++", "c++abi", "gmp", "uv", "icu", "m", "unwind", "psapi", "user32", "advapi32",
            "iphlpapi", "userenv", "ws2_32", "dbghelp", "ole32", "shell32", "bcrypt", "ucrtbase",
            "moldname", "mingwex", "pthread",
            // ntdll — Rust std's `Nt*` syscalls (NtCreateFile/NtWriteFile/...) resolve from the
            // generated import lib; the MinGW sysroot omits it.
            "ntdll",
        ] {
            println!("cargo:rustc-link-lib=static={name}");
        }
        // compiler-rt builtins (clang's libgcc equivalent) — note the lib stem carries the arch.
        println!("cargo:rustc-link-lib=static=clang_rt.builtins-x86_64");
    } else {
        for name in [
            "leancpp", "Init", "Std", "Lean", "leanrt", "Lake", "gmp", "uv",
        ] {
            println!("cargo:rustc-link-lib=static={name}");
        }
        if target_os == "macos" {
            println!("cargo:rustc-link-lib=dylib=c++");
        } else {
            // Lean's Linux toolchain compiles its C++ (leancpp et al.) against the
            // BUNDLED LLVM libc++ (`std::__1::` ABI), shipped as static archives in
            // the sysroot's lib/ (already on the search path above). Linking the
            // GNU libstdc++ instead leaves `std::__1::cout` & friends undefined —
            // the first-ever Linux link of the full archive (Convergence round 6)
            // caught exactly that. Order matters: c++ before c++abi.
            println!("cargo:rustc-link-lib=static=c++");
            println!("cargo:rustc-link-lib=static=c++abi");
        }
    }
}

/// Emit the Windows-MinGW (`x86_64-pc-windows-gnu`) link SEARCH PATHS + generate the
/// import-lib shim the Rust-gnu link needs beyond what the Lean LLVM-MinGW sysroot ships.
///
/// The Lean Windows toolchain bundles a near-complete MinGW sysroot in `$SYSROOT/lib`
/// (kernel32/user32/ws2_32/advapi32/... import libs + libc++/gmp/uv/icu + the runtime),
/// plus the compiler-rt builtins under `lib/clang/19/lib/windows`. Two libs Rust-gnu's
/// `std` + the `crt2.o` startup reference are NOT in that sysroot:
///   * `libntdll.a` — std's `Nt*` syscall imports. We synthesise a full import lib from the
///     live `ntdll.dll` export table via `llvm-dlltool` (the 2500-symbol set).
///   * `libgcc.a` / `libgcc_eh.a` — GCC's builtins/unwinder. LLVM-MinGW uses compiler-rt +
///     libunwind instead, so empty stub archives satisfy the `-lgcc`/`-lgcc_eh` the Rust-gnu
///     driver always emits (the real builtins come from `clang_rt.builtins`, the real EH from
///     `libunwind`, both linked above).
///
/// The generated shims live in `$OUT_DIR/mingw-shim`. Idempotent (regenerated each build is
/// cheap). All paths use the sysroot discovered by `lean_sysroot()`; nothing is hardcoded.
fn windows_gnu_link_env(sysroot: &Path) {
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR set by cargo"));
    let lib = sysroot.join("lib");
    let lean_lib = lib.join("lean");
    let builtins = lib.join("clang").join("19").join("lib").join("windows");
    for dir in [&lean_lib, &lib, &builtins] {
        println!("cargo:rustc-link-search=native={}", dir.display());
    }

    let shim = out_dir.join("mingw-shim");
    let _ = std::fs::create_dir_all(&shim);
    println!("cargo:rustc-link-search=native={}", shim.display());

    // Empty libgcc / libgcc_eh stubs (LLVM-MinGW has no GCC builtins; satisfy the driver's
    // unconditional `-lgcc -lgcc_eh`).
    for stub in ["libgcc.a", "libgcc_eh.a"] {
        let p = shim.join(stub);
        if !p.exists() {
            let _ = Command::new(ar_tool()).arg("rcs").arg(&p).status();
        }
    }

    // libntdll.a — synthesise from the live ntdll.dll export table. We need `llvm-dlltool`;
    // it ships in both the Lean toolchain `bin/` and a stock LLVM install. Skip (leave any
    // prior shim) if it is absent — the link then surfaces the missing `Nt*` loudly.
    let ntdll = shim.join("libntdll.a");
    if !ntdll.exists() {
        let sysntdll = PathBuf::from(r"C:\Windows\System32\ntdll.dll");
        if let Ok(out) = Command::new("llvm-objdump")
            .arg("-p")
            .arg(&sysntdll)
            .output()
        {
            let text = String::from_utf8_lossy(&out.stdout);
            let mut names = Vec::new();
            let mut in_table = false;
            for line in text.lines() {
                if line.contains("Ordinal") && line.contains("RVA") && line.contains("Name") {
                    in_table = true;
                    continue;
                }
                if in_table {
                    let toks: Vec<&str> = line.split_whitespace().collect();
                    if toks.len() >= 3
                        && toks[2]
                            .chars()
                            .next()
                            .map(|c| c.is_ascii_alphabetic() || c == '_')
                            .unwrap_or(false)
                    {
                        names.push(toks[2].to_string());
                    }
                }
            }
            if !names.is_empty() {
                let def = shim.join("ntdll.def");
                let mut body = String::from("LIBRARY ntdll.dll\nEXPORTS\n");
                for n in &names {
                    body.push_str(n);
                    body.push('\n');
                }
                if std::fs::write(&def, body).is_ok() {
                    let _ = Command::new("llvm-dlltool")
                        .args(["-d"])
                        .arg(&def)
                        .arg("-l")
                        .arg(&ntdll)
                        .args(["-m", "i386:x86-64"])
                        .status();
                }
            }
        }
        if !ntdll.exists() {
            println!(
                "cargo:warning=dregg-lean-ffi: could not synthesise libntdll.a (llvm-dlltool / \
                 llvm-objdump on PATH? ntdll.dll readable?) — the Windows-gnu link may fail on \
                 std's Nt* imports."
            );
        }
    }
}
