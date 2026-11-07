#!/bin/sh
# The direct-logic compiler without a native build: `lake env lean --run DirectLogicCompile.lean`,
# which interprets the same `respond` the `direct_logic_compile` executable compiles. Slow to
# start (it loads the module's olean closure); for corpus regeneration and machines without the
# native executable. Point DREGG_DIRECT_LOGIC_COMPILER at this script to use it from Rust.
cd "$(dirname "$0")/.." && exec lake env lean --run DirectLogicCompile.lean
