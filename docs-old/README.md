# docs-old — archived design & audit notes (NOT authoritative)

These markdown files were the project's top-level design, audit, and planning
documents during active development. They were written across many sessions by
several different authors and models, and they describe what someone *intended or
believed at the moment of writing*. They are kept here for history.

**Do not treat anything in this directory as current ground truth.** These docs
routinely:

- describe partial work as finished,
- omit features that already shipped,
- propose designs that were never built (or built differently),
- contradict each other across dates.

For what is actually true, in order of authority:

1. the **code and tests** (they compile and run; the docs do not);
2. [`../STATUS.md`](../STATUS.md) — a small, code-verified status file;
3. nothing else.

Original file modification times were preserved when these were moved here, so an
`ls -lt` reflects roughly when each was last touched — useful for judging how stale a
given note is. Many source files still carry `//! see SOME-DOC.md` comments that now
resolve to this directory; those pointers are design-intent references, not promises
that the code matches the doc.
