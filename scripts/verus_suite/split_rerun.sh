#!/bin/bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# Examples whose file stems collide share one test_inputs dir name (example-<stem>),
# so their shim events land in one file. Re-run each such test alone, with ay and
# with z3 behind the measurement shim, into <out-root>/runs/<label>/split/<test>/ and
# <out-root>/runs/<z3-label>/split/<test>/. Pairs are run one member at a time so the
# two never share the directory at once.
#
#   split_rerun.sh <label> [<z3-label, default z3-shim>]
#
# AY_BIN is required (no default). Both sides run in the stage of <z3-label>; the out
# root is VERUS_SUITE_OUT_ROOT (default: .verus-suite/ at the repo root). Other shim
# options (AY_SHIM_DROP_STDERR, AY_SHIM_RLIMIT_MONOTONE, ...) pass through. When
# run_one.sh refuses (no stage, no library, ...) this stops with its message and exit 2.
set -u
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd "$here/../.." && pwd)
root=${VERUS_SUITE_OUT_ROOT:-$repo/.verus-suite}
[ $# -ge 1 ] || { echo "usage: split_rerun.sh <label> [<z3-label>]" >&2; exit 2; }
label=$1
ref=${2:-z3-shim}
if [ -z "${AY_BIN:-}" ]; then
  echo "split_rerun.sh: AY_BIN is required and has no default: set it to the ay binary the run <$label> measured" >&2
  exit 2
fi
first="examples_assert_by_compute examples_calc examples_datatypes examples_integers examples_invariants examples_overflow examples_recursion examples_state_machines_tutorial_counting_to_2 examples_state_machines_tutorial_counting_to_n examples_state_machines_tutorial_fifo examples_state_machines_tutorial_rc"
second="examples_guide_assert_by_compute examples_guide_calc examples_guide_datatypes examples_guide_integers examples_guide_invariants examples_guide_overflow examples_guide_recursion examples_state_machines_tutorial_unverified_counting_to_2 examples_state_machines_tutorial_unverified_counting_to_n examples_state_machines_tutorial_unverified_fifo examples_state_machines_tutorial_unverified_rc"
export VERUS_SUITE_OUT_ROOT=$root AY_BIN AY_SHIM_ARGS="${AY_SHIM_ARGS:--q --z3-mode}" AY_SHIM_QUERY_WALL_S=${AY_SHIM_QUERY_WALL_S:-60}
for group in "$first" "$second"; do
  for t in $group; do
    if ! err=$("$here/run_one.sh" "$ref" z3 "$root/runs/$ref/split/examples-$t" examples "$t" 2>&1 >/dev/null); then
      echo "split_rerun.sh: stopped: $err" >&2
      exit 2
    fi
  done
  # xargs exits non-zero when any run_one.sh did (pipefail keeps its status past sed)
  if ! printf '%s\n' $group | xargs -P 3 -I{} bash -c 'set -o pipefail; "$0" "$1" ay "$2/examples-$3" examples "$3" 2>&1 | sed "s/^/$3: /"' \
       "$here/run_one.sh" "$ref" "$root/runs/$label/split" {}; then
    echo "split_rerun.sh: stopped: run_one.sh refused at least one ay run (its message is above)" >&2
    exit 2
  fi
done
