# The lane loop's Lean checks (BUILD.md). Both drive scripts/iter-check.
#   make check-fast              changed .lean files, here (the Mac): imports warm, then `lake lean` per file
#   make check-full              changed modules + every in-tree module importing them, on the least-loaded box
#   make check-umbrella          the default targets (lakefile defaultTargets), on bb2 only
#   make boxes                   the box table check-full chooses from
# FILES="A.lean B.lean" restricts either check to those files.
.PHONY: check-fast check-full check-umbrella boxes
check-fast:
	@python3 scripts/iter-check fast $(FILES)
check-full:
	@python3 scripts/iter-check full $(FILES)
check-umbrella:
	@python3 scripts/iter-check full --umbrella
boxes:
	@python3 scripts/iter-check boxes
