#!/bin/bash
# Build upstream Verus's builtin crates with trustc, for staging under
# target-verus/<profile>/ where upstream's test harness looks for them.
#
# Usage: build_verus_builtins.sh OUT_DIR [VERUS_ROOT]
#
# Produces in OUT_DIR:
#   libverus_builtin.rlib
#   libverus_builtin_macros.dylib
#   libverus_state_machines_macros.dylib
# plus the rlibs of their dependencies.
#
# Upstream's own copies were built by rustc 1.95 and trustc rejects them
# (E0514), so every crate the test crate links must come from trustc.
#
# No cargo build: the upstream workspace is read-only here, so each crate is
# one trustc invocation. Registry versions come from Verus's Cargo.lock, never
# whichever compatible version happens to be cached. Sources come from Cargo's
# registry or checksum-verified .crate archives, unpacked under OUT_DIR/src.
# An archive may also be supplied as OUT_DIR/src/NAME-VERSION.crate. To use a
# linker other than trustc's default, set TRUST_VC_BUILTINS_LINKER to its path.
#
# Every unit is built with -Ztrust-verify=off: these are proc macros and a
# marker library that the test crate links, not verification targets.
#
# The cfg set mirrors what vargo builds with (tools/vargo/src/commands/mod.rs,
# rust_flags): proc_macro_span, verus_keep_ghost, span_locations,
# procmacro2_semver_exempt, applied to every crate. Build-script outputs that
# vargo's cargo run would have produced are passed as explicit --cfg flags.
set -euo pipefail

OUT=${1:?usage: build_verus_builtins.sh OUT_DIR [VERUS_ROOT]}
# The Verus checkout, found as run_suite.py finds it: the argument, then
# TRUST_VC_VERUS_PATH, then VERUS_PATH, then ../verus beside this repository.
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
V=${2:-${TRUST_VC_VERUS_PATH:-${VERUS_PATH:-$repo/../verus}}}
[ -d "$V/source/builtin" ] || { echo "no Verus checkout at $V" >&2; exit 2; }
mkdir -p "$OUT/src"
OUT=$(cd "$OUT" && pwd)

registry_home=${CARGO_HOME:-$HOME/.cargo}

registry_source() {
  local name=$1 major=$2 locked version checksum archive actual source
  locked=$(awk -v wanted="$name" -v major="$major" '
    /^\[\[package\]\]$/ { name = ""; version = "" }
    /^name = / { name = $3; gsub(/"/, "", name) }
    /^version = / { version = $3; gsub(/"/, "", version) }
    /^checksum = / {
      if (name == wanted && index(version, major ".") == 1) {
        checksum = $3; gsub(/"/, "", checksum)
        print version, checksum
      }
    }
  ' "$V/source/Cargo.lock")
  if [[ -z "$locked" || "$locked" == *$'\n'* ]]; then
    echo "expected exactly one registry $name $major.x in $V/source/Cargo.lock" >&2
    return 2
  fi
  read -r version checksum <<< "$locked"
  for archive in "$OUT/src/$name-$version.crate" \
      "$registry_home"/registry/cache/*/"$name-$version.crate"; do
    [ -f "$archive" ] || continue
    actual=$(shasum -a 256 "$archive")
    if [ "${actual%% *}" != "$checksum" ]; then
      echo "checksum mismatch for $archive (expected $checksum)" >&2
      return 2
    fi
    # Re-extract the verified archive so an old output source tree cannot
    # silently override its authenticated contents.
    tar xzf "$archive" -C "$OUT/src"
    [ -f "$OUT/src/$name-$version/src/lib.rs" ] || {
      echo "archive has no $name-$version/src/lib.rs: $archive" >&2
      return 2
    }
    echo "$OUT/src/$name-$version"
    return
  done
  for source in "$registry_home"/registry/src/*/"$name-$version"; do
    if [ -f "$source/src/lib.rs" ]; then
      echo "$source"
      return
    fi
  done
  echo "missing locked registry source $name $version; fetch the upstream locked dependencies or place $name-$version.crate in $OUT/src" >&2
  return 2
}

UNICODE_IDENT=$(registry_source unicode-ident 1)
PROC_MACRO2=$(registry_source proc-macro2 1)
QUOTE=$(registry_source quote 1)
SYN=$(registry_source syn 2)
SYNSTRUCTURE=$(registry_source synstructure 0)
INDEXMAP=$(registry_source indexmap 1)
HASHBROWN=$(registry_source hashbrown 0.12)

# vargo's RUSTFLAGS, applied to every unit.
VARGO_CFGS=(--cfg proc_macro_span --cfg verus_keep_ghost --cfg span_locations --cfg procmacro2_semver_exempt)

T=(trustc -Ztrust-verify=off --cap-lints allow -C debuginfo=0 --out-dir "$OUT" -L "dependency=$OUT" "${VARGO_CFGS[@]}")
if [ -n "${TRUST_VC_BUILTINS_LINKER:-}" ]; then
  T+=(-C "linker=$TRUST_VC_BUILTINS_LINKER")
fi

LOG=$OUT/build.log
: > "$LOG"

run() {
  local name=$1
  shift
  echo ">> $name" | tee -a "$LOG"
  if ! "${T[@]}" "$@" >>"$LOG" 2>&1; then
    echo "FAILED: $name (see $LOG)" >&2
    tail -30 "$LOG" >&2
    exit 1
  fi
}

run unicode_ident --edition 2021 --crate-type rlib --crate-name unicode_ident \
  "$UNICODE_IDENT/src/lib.rs"

# proc-macro2's build.rs, on a dev compiler with procmacro2_semver_exempt set,
# emits exactly these cfgs.
run proc_macro2 --edition 2021 --crate-type rlib --crate-name proc_macro2 \
  --cfg 'feature="proc-macro"' --cfg 'feature="default"' \
  --cfg wrap_proc_macro --cfg proc_macro_span_location --cfg proc_macro_span_file \
  --cfg super_unstable \
  --extern unicode_ident="$OUT/libunicode_ident.rlib" \
  "$PROC_MACRO2/src/lib.rs"

run quote --edition 2021 --crate-type rlib --crate-name quote \
  --cfg 'feature="proc-macro"' --cfg 'feature="default"' \
  --extern proc_macro2="$OUT/libproc_macro2.rlib" \
  "$QUOTE/src/lib.rs"

SYNF=(--cfg 'feature="full"' --cfg 'feature="visit"' --cfg 'feature="visit-mut"'
  --cfg 'feature="extra-traits"' --cfg 'feature="parsing"' --cfg 'feature="printing"'
  --cfg 'feature="clone-impls"' --cfg 'feature="proc-macro"' --cfg 'feature="derive"'
  --cfg 'feature="default"')

run syn --edition 2021 --crate-type rlib --crate-name syn "${SYNF[@]}" \
  --extern proc_macro2="$OUT/libproc_macro2.rlib" --extern quote="$OUT/libquote.rlib" \
  --extern unicode_ident="$OUT/libunicode_ident.rlib" \
  "$SYN/src/lib.rs"

run synstructure --edition 2018 --crate-type rlib --crate-name synstructure \
  --cfg 'feature="proc-macro"' --cfg 'feature="default"' \
  --extern proc_macro2="$OUT/libproc_macro2.rlib" --extern quote="$OUT/libquote.rlib" \
  --extern syn="$OUT/libsyn.rlib" --extern unicode_ident="$OUT/libunicode_ident.rlib" \
  "$SYNSTRUCTURE/src/lib.rs"

run verus_syn --edition 2021 --crate-type rlib --crate-name verus_syn \
  --cfg check_cfg "${SYNF[@]}" \
  --extern proc_macro2="$OUT/libproc_macro2.rlib" --extern quote="$OUT/libquote.rlib" \
  --extern unicode_ident="$OUT/libunicode_ident.rlib" \
  "$V/dependencies/syn/src/lib.rs"

run verus_prettyplease --edition 2021 --crate-type rlib --crate-name verus_prettyplease \
  --extern proc_macro2="$OUT/libproc_macro2.rlib" --extern verus_syn="$OUT/libverus_syn.rlib" \
  "$V/dependencies/prettyplease/src/lib.rs"

run verus_builtin --edition 2018 --crate-type rlib --crate-name verus_builtin \
  "$V/source/builtin/src/lib.rs"

run verus_builtin_macros --edition 2018 --crate-type proc-macro --crate-name verus_builtin_macros \
  --extern proc_macro \
  --extern proc_macro2="$OUT/libproc_macro2.rlib" --extern quote="$OUT/libquote.rlib" \
  --extern syn="$OUT/libsyn.rlib" --extern synstructure="$OUT/libsynstructure.rlib" \
  --extern verus_syn="$OUT/libverus_syn.rlib" \
  --extern verus_prettyplease="$OUT/libverus_prettyplease.rlib" \
  "$V/source/builtin_macros/src/lib.rs"

run hashbrown --edition 2021 --crate-type rlib --crate-name hashbrown \
  --cfg 'feature="raw"' \
  "$HASHBROWN/src/lib.rs"

# indexmap's build.rs emits has_std when std is available (always, here).
run indexmap --edition 2021 --crate-type rlib --crate-name indexmap \
  --cfg has_std --cfg 'feature="std"' \
  --extern hashbrown="$OUT/libhashbrown.rlib" \
  "$INDEXMAP/src/lib.rs"

run verus_state_machines_macros --edition 2018 --crate-type proc-macro \
  --crate-name verus_state_machines_macros \
  --extern proc_macro \
  --extern proc_macro2="$OUT/libproc_macro2.rlib" --extern quote="$OUT/libquote.rlib" \
  --extern verus_syn="$OUT/libverus_syn.rlib" --extern indexmap="$OUT/libindexmap.rlib" \
  "$V/source/state_machines_macros/src/lib.rs"

# Record which compiler built these, so a stale staging is detectable.
trustc -vV > "$OUT/trustc-version.txt"
ls -la "$OUT"/libverus_builtin.rlib "$OUT"/libverus_builtin_macros.dylib \
  "$OUT"/libverus_state_machines_macros.dylib
