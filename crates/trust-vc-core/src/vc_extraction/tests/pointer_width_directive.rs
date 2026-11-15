// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Source-level wiring of the `global size_of usize == N` architecture
//! directive (#2778).
//!
//! These tests drive the directive through the production source-unit entry
//! point [`verify_function_from_file`], proving that a `global size_of usize ==
//! N;` line in a verified unit actually installs the usize/isize bit-width for
//! that unit's verification — proving width-specific facts and refuting facts
//! that only hold at a different width. They complement the in-process guard
//! mechanics tested in `ir_tests.rs` and the encoder-level shift cases in
//! `encoder/tests/shift_soundness.rs`, which install the width programmatically
//! rather than from source.

use super::super::*;
use crate::encoder::VerifyResult;
use std::fs;
use std::path::PathBuf;

/// Writes `code` to a uniquely named fixture file and returns its path.
fn write_fixture(name: &str, code: &str) -> PathBuf {
    let dir = PathBuf::from("target/test_pointer_width_directive");
    fs::create_dir_all(&dir).expect("create pointer-width fixture dir");
    let path = dir.join(name);
    fs::write(&path, code).expect("write pointer-width fixture");
    path
}

/// Under `global size_of usize == 4`, every `usize` is a 32-bit value, so
/// `x < 2^32` (a 32-bit-specific fact) is a theorem and verifies. This is the
/// source-level analogue of upstream `bit_shift_overflow_arch32`.
#[test]
fn arch32_directive_proves_32bit_usize_bound() {
    let path = write_fixture(
        "arch32_proves_lt_2pow32.rs",
        "global size_of usize == 4;\n\
         #[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x < 4294967296);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "under `global size_of usize == 4`, every usize is < 2^32 and the \
         assertion must verify, got {result:?}"
    );
}

/// The SAME unit/source under `global size_of usize == 8` makes `usize` a 64-bit
/// value, so `x < 2^32` is no longer a theorem: a usize larger than `u32::MAX`
/// is a valid counterexample. Refuting here (rather than spuriously verifying)
/// is what proves the directive actually re-installed the width.
#[test]
fn arch64_directive_refutes_32bit_only_usize_bound() {
    let path = write_fixture(
        "arch64_refutes_lt_2pow32.rs",
        "global size_of usize == 8;\n\
         #[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x < 4294967296);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "under `global size_of usize == 8`, x < 2^32 is NOT a theorem and must \
         be refuted, got {result:?}"
    );
}

/// Vice-versa: under `global size_of usize == 8`, a usize *can* exceed
/// `u32::MAX`, so a precondition pinning `x > u32::MAX` is satisfiable and the
/// implied 64-bit-specific fact `x >= 2^32` verifies.
#[test]
fn arch64_directive_proves_64bit_only_usize_fact() {
    let path = write_fixture(
        "arch64_proves_ge_2pow32.rs",
        "global size_of usize == 8;\n\
         #[trust_vc::proof]\n\
         #[requires(x > 4294967295)]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x >= 4294967296);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "under `global size_of usize == 8`, `x > u32::MAX` is reachable and \
         implies x >= 2^32, which must verify, got {result:?}"
    );
}

/// The mirror of the previous case: under `global size_of usize == 4`, that same
/// 64-bit-only precondition `x > u32::MAX` is *unsatisfiable* (no 32-bit usize
/// exceeds `u32::MAX`). The verifier must NOT spuriously report `Verified` as
/// though the proof were reachable; it flags the premise as contradictory. This
/// confirms the width genuinely changed the model rather than carrying over.
#[test]
fn arch32_directive_makes_64bit_only_precondition_contradictory() {
    let path = write_fixture(
        "arch32_contradicts_ge_2pow32.rs",
        "global size_of usize == 4;\n\
         #[trust_vc::proof]\n\
         #[requires(x > 4294967295)]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x >= 4294967296);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    assert!(
        matches!(
            result,
            VerifyResult::Unknown {
                category: crate::UnknownCategory::VacuousTruth,
                ..
            }
        ),
        "under `global size_of usize == 4`, `x > u32::MAX` is unsatisfiable; the \
         verifier must flag the contradictory premise, not spuriously verify, \
         got {result:?}"
    );
}

/// Without any directive, a `usize`-typed unit is pointer-width polymorphic, so
/// the proof must hold for BOTH a 32-bit and a 64-bit `usize` (#2778 dual-arch).
/// The 32-bit-only bound `x < 2^32` holds at 32-bit but is refuted at 64-bit, so
/// the combined verdict is a counterexample — *regardless of host width* — and is
/// tagged `_64bit` to record that the 64-bit arch is the one that fails. This is
/// the soundness upgrade over the old "host width only" behavior, which would
/// spuriously verify a 64-bit-only fact on a 64-bit host.
#[test]
fn no_directive_requires_both_archs() {
    let path = write_fixture(
        "no_directive_dual_arch.rs",
        "#[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x < 4294967296);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.ends_with("_64bit"),
            "the 64-bit arch is the failing one; the obligation name must be \
             tagged `_64bit`, got {obligation_name:?}"
        ),
        other => panic!(
            "without a directive, `x < 2^32` must be refuted on the 64-bit arch \
             (dual-width), got {other:?}"
        ),
    }
}

/// A malformed directive (`== 5` bytes → 40-bit usize, which Rust never uses)
/// must fail closed at the source surface rather than verify against an
/// unrealizable target.
#[test]
fn malformed_directive_fails_closed() {
    let path = write_fixture(
        "malformed_directive.rs",
        "global size_of usize == 5;\n\
         #[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x == x);\n\
         }\n",
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "f");
    let err = result.expect_err("a malformed directive must fail closed");
    let msg = err.to_string();
    assert!(
        msg.contains("unsupported usize size"),
        "malformed directive should report the unsupported width, got {msg}"
    );
}

/// Two conflicting `global size_of usize` directives describe an impossible
/// target and must fail closed instead of silently choosing one.
#[test]
fn conflicting_directives_fail_closed() {
    let path = write_fixture(
        "conflicting_directives.rs",
        "global size_of usize == 4;\n\
         global size_of usize == 8;\n\
         #[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x == x);\n\
         }\n",
    );

    let result = verify_function_from_file(path.to_str().unwrap(), "f");
    let err = result.expect_err("conflicting directives must fail closed");
    let msg = err.to_string();
    assert!(
        msg.contains("conflicting"),
        "conflicting directives should be reported, got {msg}"
    );
}

/// The directive line is a unit-level pragma, not a Rust item: it must be
/// stripped before parsing (so the parser never chokes on it) yet the
/// surrounding code must still parse and verify. This pins the strip-then-parse
/// behavior end to end.
#[test]
fn directive_line_is_stripped_before_parsing() {
    let path = write_fixture(
        "directive_stripped.rs",
        "global size_of usize == 4;\n\
         #[trust_vc::proof]\n\
         #[ensures(result == x)]\n\
         fn ident(x: usize) -> usize {\n\
        \x20   x\n\
         }\n",
    );

    // If the directive were not stripped, `parse_file_allow_tracked` would error
    // on the non-Rust `global ...` line. Reaching a Verified verdict proves the
    // line was both consumed (for width) and removed (for parsing).
    let result = verify_function_from_file(path.to_str().unwrap(), "ident")
        .expect("verification should run after stripping the directive line");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a unit carrying a valid directive must still parse and verify the body, \
         got {result:?}"
    );
}

/// The directive must not leak past the unit that declared it: after a
/// `== 4` unit verifies, a subsequent directive-free unit on a 64-bit host must
/// see the host width again. Verifying these back to back in one test pins the
/// RAII restore behavior at the source surface.
#[test]
fn directive_does_not_leak_to_next_unit() {
    let with_dir = write_fixture(
        "leak_unit_with_directive.rs",
        "global size_of usize == 4;\n\
         #[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x < 4294967296);\n\
         }\n",
    );
    let _ = verify_function_from_file(with_dir.to_str().unwrap(), "f")
        .expect("first unit verification should run");

    let without_dir = write_fixture(
        "leak_unit_without_directive.rs",
        "#[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x < 4294967296);\n\
         }\n",
    );
    let after =
        verify_function_from_file(without_dir.to_str().unwrap(), "f").expect("second unit runs");
    // The directive-free second unit is verified dual-width (both archs required),
    // so the 32-bit-only bound `x < 2^32` is refuted on the 64-bit arch. The
    // critical leak check is that the FIRST unit's `== 4` (32-bit) width does not
    // carry over: if it had, the 64-bit pass would never run and the unit would
    // spuriously verify. A `_64bit`-tagged counterexample proves the 64-bit pass
    // ran with a fresh (non-leaked) width.
    match after {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.ends_with("_64bit"),
            "the 32-bit width from the first unit must NOT leak; the second unit's \
             64-bit pass must run and refute the bound, got {obligation_name:?}"
        ),
        other => panic!(
            "the second (directive-free) unit must be verified dual-width and \
             refuted on the 64-bit arch, got {other:?}"
        ),
    }
}

// --------------------------------------------------------------------------
// Dual-width (#2778) usize-polymorphic encoding: when a directive-free unit
// mentions `usize`/`isize`, Rust permits both a 32-bit and a 64-bit target, so
// the obligation set is emitted at BOTH widths and a `Verified` verdict requires
// BOTH to discharge. Failures are surfaced with the arch(es) on which they fail
// (`_32bit` / `_64bit` / `_32bit_64bit`), mirroring upstream Verus's
// `assert_fails_bv_32bit`/`_64bit`/`_32bit_64bit` reporting. These cases drive
// the same proof shapes as upstream `bit_vector_with_usize_valid_expr` and the
// `bit_vector_usize_as_{32,64}bit` cluster in
// `../verus/source/rust_verify_test/tests/bitvector.rs`.

/// Should-verify direction: a width-invariant fact about `usize` (`x & x == x`)
/// holds at BOTH a 32-bit and a 64-bit `usize`, so the combined dual-width
/// verdict is `Verified`. This is the dual-width analogue of upstream
/// `usize_in_by_bit_vector` (`assert(x & x == x) by(bit_vector)` => Ok).
#[test]
fn dual_width_verifies_when_fact_holds_at_both_widths() {
    let path = write_fixture(
        "dual_both_archs_ok.rs",
        "#[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!((x & x) == x);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "`x & x == x` holds at both 32-bit and 64-bit usize; the combined \
         dual-width verdict must be Verified, got {result:?}"
    );
}

/// Should-fail direction, 64-bit arch only: `(x >> 32) == 0usize` holds when
/// `usize` is 32-bit (the whole value is shifted out) but is refuted when `usize`
/// is 64-bit (the high 32 bits survive). The dual-width verdict is therefore a
/// counterexample tagged `_64bit`. Upstream parity: `bit_vector_with_usize_valid_expr::test_usize4`.
#[test]
fn dual_width_refutes_64bit_only_shift_fact_with_arch_tag() {
    let path = write_fixture(
        "dual_shr32_64bit_fail.rs",
        "#[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!((x >> 32) == 0);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.ends_with("_64bit") && !obligation_name.ends_with("_32bit_64bit"),
            "the shift fact fails only on the 64-bit arch; the obligation name \
             must be tagged `_64bit` (not `_32bit_64bit`), got {obligation_name:?}"
        ),
        other => panic!(
            "`(x >> 32) == 0` must be refuted on the 64-bit arch (dual-width), \
             got {other:?}"
        ),
    }
}

/// Should-fail direction, both archs: `x < x` is false for some `usize` at EVERY
/// width, so both the 32-bit and 64-bit passes produce a counterexample and the
/// combined verdict is tagged `_32bit_64bit`.
#[test]
fn dual_width_refutes_universally_false_fact_with_both_arch_tag() {
    let path = write_fixture(
        "dual_both_fail.rs",
        "#[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x < x);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.ends_with("_32bit_64bit"),
            "`x < x` is false at both widths; the obligation name must be tagged \
             `_32bit_64bit`, got {obligation_name:?}"
        ),
        other => panic!("`x < x` must be refuted at both widths, got {other:?}"),
    }
}

/// Should-fail direction, 32-bit arch only (fail-closed Unknown): a 64-bit-only
/// precondition `x >= 2^32` is reachable for a 64-bit `usize` (so the implied
/// fact verifies there) but is *unsatisfiable* for a 32-bit `usize`. Rather than
/// let the 64-bit success mask the 32-bit contradiction, the combined dual-width
/// verdict surfaces the 32-bit `VacuousTruth` Unknown, tagged `arch_32bit`. This
/// pins the fail-closed combination rule: a non-verifying outcome on either width
/// is never swallowed by the other width's success.
#[test]
fn dual_width_surfaces_32bit_only_vacuous_premise_fail_closed() {
    let path = write_fixture(
        "dual_32bit_vacuous.rs",
        "#[trust_vc::proof]\n\
         #[requires(x >= 4294967296)]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!(x >= 4294967296);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    match result {
        VerifyResult::Unknown { reason, category } => {
            assert_eq!(
                category,
                crate::UnknownCategory::VacuousTruth,
                "the 32-bit premise is contradictory, got reason {reason:?}"
            );
            assert!(
                reason.contains("arch_32bit") && !reason.contains("arch_32bit_64bit"),
                "the contradiction is 32-bit-only and must be tagged `arch_32bit` \
                 (not `arch_32bit_64bit`), got {reason:?}"
            );
        }
        other => panic!(
            "a 64-bit-only precondition must surface a fail-closed 32-bit Unknown \
             (not be masked by the 64-bit pass), got {other:?}"
        ),
    }
}

/// A unit that names no `usize`/`isize` is NOT pointer-width polymorphic, so it is
/// verified once (at the host width) — the dual-width path must not engage and the
/// obligation name must carry no arch suffix. Guards against the polymorphism
/// detector over-firing and double-verifying width-invariant units.
#[test]
fn non_usize_unit_is_not_dual_width() {
    let path = write_fixture(
        "non_usize_single_width.rs",
        "#[trust_vc::proof]\n\
         fn f(x: u32) {\n\
        \x20   trust_vc::assert!(x < x);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            !obligation_name.ends_with("_32bit")
                && !obligation_name.ends_with("_64bit")
                && !obligation_name.ends_with("_32bit_64bit"),
            "a non-usize unit must be verified single-width with no arch suffix, \
             got {obligation_name:?}"
        ),
        other => panic!("`x < x` over u32 must be refuted, got {other:?}"),
    }
}

/// A unit carrying a pinned `global size_of usize == N` directive fixes the
/// target arch and must be verified EXACTLY ONCE at that width — the dual-width
/// path must not engage even though the unit mentions `usize`. Under `== 8`
/// (64-bit), `(x >> 32) == 0` is refuted, and the counterexample must carry NO
/// arch suffix (single pinned width, not a dual-width combination).
#[test]
fn pinned_directive_stays_single_width_no_arch_tag() {
    let path = write_fixture(
        "pinned_single_width.rs",
        "global size_of usize == 8;\n\
         #[trust_vc::proof]\n\
         fn f(x: usize) {\n\
        \x20   trust_vc::assert!((x >> 32) == 0);\n\
         }\n",
    );

    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            !obligation_name.ends_with("_32bit")
                && !obligation_name.ends_with("_64bit")
                && !obligation_name.ends_with("_32bit_64bit"),
            "a pinned-directive unit is verified single-width; the counterexample \
             must carry no arch suffix, got {obligation_name:?}"
        ),
        other => panic!("under pinned `== 8`, `(x >> 32) == 0` must be refuted, got {other:?}"),
    }
}

// --------------------------------------------------------------------------
// Architecture-width SHIFT-BOUND scout cases driven by the `global size_of
// usize == N` directive (#2778, cluster #2778).
//
// Upstream Verus `overflow.rs::bit_shift_overflow_arch32` /
// `bit_shift_overflow_arch64` pin a target pointer width with
// `global size_of usize == N;` and then check that an `exec` `usize` left shift
// by the bit width (`<< 32` at 32-bit, `<< 64` at 64-bit) FAILS as a possible
// shift overflow (shift-by->=width is UB in every Rust mode), while a shift by
// `width - 1` (`<< 31` / `<< 63`) verifies.
//
// These are exec functions: a bit shift is UB only in exec code, so the shift
// bound (`BitshiftBehavior::Error`, the exec default) fires for them — a
// `#[trust_vc::proof]` function is int-mode where shift UB does not exist
// (`BitshiftBehavior::Allow`) and would (soundly) verify the over-shift. The
// fixtures below therefore use a plain `fn` and reach the same already-landed,
// independently-tested exec shift-overflow checker
// (`encoder::operators::check_shift_overflow`, validated programmatically in
// `encoder/tests/shift_soundness.rs::test_usize_shl_by_*`). The only new surface
// is the *source-directive* driving of the LHS width: the directive both fixes
// the `usize` width baked into the IR (the counterexample binding type is `u32`
// at `== 4` and `u64` at `== 8`) AND the bound the shift check compares against.
//
// Soundness is by construction: an in-range shift verifies and an out-of-range
// shift fails closed; the directive only *changes the width* the existing check
// uses (the cross-width control below shows `<< 32` failing at `== 4` but
// verifying at `== 8`), so nothing is weakened and no over-shift can slip
// through. Mirrors upstream byte-for-byte: `<< (BITS-1)` Ok, `<< BITS` FAILS.

/// Reusable exec-mode fixture: a plain `fn f(x: usize)` under
/// `global size_of usize == N` whose body performs `x << AMT`. Exec mode is what
/// makes the shift bound fire (see the section header).
fn arch_shift_fixture(name: &str, size_of_bytes: u32, shift_amount: u32) -> PathBuf {
    write_fixture(
        name,
        &format!(
            "global size_of usize == {size_of_bytes};\n\
             fn f(x: usize) {{\n\
            \x20   let _ = x << {shift_amount}usize;\n\
             }}\n"
        ),
    )
}

/// SHOULD-FAIL, arch32: under `global size_of usize == 4`, `usize` is 32-bit, so
/// `x << 32` shifts by the full bit width — UB — and must fail closed as a
/// possible left shift overflow. The counterexample binding type pins the width
/// to `u32`, proving the directive (not the host) set the LHS width. Mirrors
/// upstream `bit_shift_overflow_arch32` (the `// FAILS` line).
#[test]
fn arch32_directive_refutes_usize_shift_by_bitwidth() {
    let path = arch_shift_fixture("arch32_shl_by_32_fails.rs", 4, 32);
    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    match result {
        VerifyResult::Counterexample {
            obligation_name,
            bindings,
            ..
        } => {
            assert!(
                obligation_name.contains("left shift overflow"),
                "under `== 4`, `x << 32` is UB and must fail closed as a possible \
                 left shift overflow, got obligation {obligation_name:?}"
            );
            // A pinned directive verifies once at the fixed width: no arch suffix.
            assert!(
                !obligation_name.ends_with("_32bit")
                    && !obligation_name.ends_with("_64bit")
                    && !obligation_name.ends_with("_32bit_64bit"),
                "a pinned-directive unit is single-width; the counterexample must \
                 carry no arch suffix, got {obligation_name:?}"
            );
            assert!(
                bindings.iter().any(|b| b.ty == "u32"),
                "`== 4` must make `usize` a 32-bit value (binding type `u32`), \
                 proving the directive set the shift width, got {bindings:?}"
            );
        }
        other => {
            panic!("under `== 4`, `x << 32` (shift by bit width) must be refuted, got {other:?}")
        }
    }
}

/// SHOULD-VERIFY, arch32: under `global size_of usize == 4`, `x << 31` shifts by
/// `width - 1` — in range — and verifies. Mirrors upstream
/// `bit_shift_overflow_arch32`'s passing line. This is the should-verify control
/// for `arch32_directive_refutes_usize_shift_by_bitwidth`.
#[test]
fn arch32_directive_verifies_usize_shift_in_range() {
    let path = arch_shift_fixture("arch32_shl_by_31_ok.rs", 4, 31);
    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "under `== 4`, `x << 31` (shift by width - 1) is in range and must \
         verify, got {result:?}"
    );
}

/// SHOULD-FAIL, arch64: under `global size_of usize == 8`, `usize` is 64-bit, so
/// `x << 64` shifts by the full bit width — UB — and must fail closed. The
/// binding type pins the width to `u64`. Mirrors upstream
/// `bit_shift_overflow_arch64` (the `// FAILS` line).
#[test]
fn arch64_directive_refutes_usize_shift_by_bitwidth() {
    let path = arch_shift_fixture("arch64_shl_by_64_fails.rs", 8, 64);
    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    match result {
        VerifyResult::Counterexample {
            obligation_name,
            bindings,
            ..
        } => {
            assert!(
                obligation_name.contains("left shift overflow"),
                "under `== 8`, `x << 64` is UB and must fail closed as a possible \
                 left shift overflow, got obligation {obligation_name:?}"
            );
            assert!(
                !obligation_name.ends_with("_32bit")
                    && !obligation_name.ends_with("_64bit")
                    && !obligation_name.ends_with("_32bit_64bit"),
                "a pinned-directive unit is single-width; the counterexample must \
                 carry no arch suffix, got {obligation_name:?}"
            );
            assert!(
                bindings.iter().any(|b| b.ty == "u64"),
                "`== 8` must make `usize` a 64-bit value (binding type `u64`), \
                 proving the directive set the shift width, got {bindings:?}"
            );
        }
        other => {
            panic!("under `== 8`, `x << 64` (shift by bit width) must be refuted, got {other:?}")
        }
    }
}

/// SHOULD-VERIFY, arch64: under `global size_of usize == 8`, `x << 63` shifts by
/// `width - 1` — in range — and verifies. Mirrors upstream
/// `bit_shift_overflow_arch64`'s passing line.
#[test]
fn arch64_directive_verifies_usize_shift_in_range() {
    let path = arch_shift_fixture("arch64_shl_by_63_ok.rs", 8, 63);
    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "under `== 8`, `x << 63` (shift by width - 1) is in range and must \
         verify, got {result:?}"
    );
}

/// CROSS-WIDTH DISCRIMINATOR: the SAME `x << 32` shift fails closed under
/// `== 4` (32 == 32-bit width, UB — see
/// `arch32_directive_refutes_usize_shift_by_bitwidth`) but VERIFIES under `== 8`
/// (32 < 64-bit width, in range). Passing only because the bound moved with the
/// directive — not because 32 happens to match the host width — is what proves
/// the directive genuinely re-installs the shift width rather than the result
/// being a host-width coincidence. Upstream parity: the arch32 vs arch64
/// over-shift threshold differs by exactly the pointer width.
#[test]
fn cross_width_same_shift_amount_flips_verdict_with_directive() {
    let path = arch_shift_fixture("arch64_shl_by_32_ok.rs", 8, 32);
    let result =
        verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run");
    assert!(
        matches!(result, VerifyResult::Verified),
        "under `== 8`, `x << 32` is in range (32 < 64) and must verify — the same \
         shift that fails under `== 4` — proving the directive moved the width, \
         got {result:?}"
    );
}

/// Combination-rule unit tests over [`combine_dual_width_results`] and the arch
/// suffix, exercising every (32-bit, 64-bit) outcome pairing directly without the
/// solver. These pin the soundness-critical rules: `Verified` requires BOTH
/// widths; any non-verifying width is surfaced (fail-closed) with the correct
/// arch tag; and a concrete counterexample is preferred over an Unknown.
#[test]
fn combine_rules_cover_all_outcome_pairings() {
    use super::super::combine_dual_width_results;

    let verified = || VerifyResult::Verified;
    let cex = |name: &str| VerifyResult::Counterexample {
        obligation_name: name.to_string(),
        location: None,
        model: None,
        bindings: Vec::new(),
    };
    let unknown = || VerifyResult::Unknown {
        reason: "stuck".to_string(),
        category: crate::UnknownCategory::Timeout,
    };

    // Both verified → Verified, no tag.
    assert!(matches!(
        combine_dual_width_results(verified(), verified()),
        VerifyResult::Verified
    ));

    // 64-bit fails (32 ok) → `_64bit` counterexample.
    match combine_dual_width_results(verified(), cex("a")) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert_eq!(obligation_name, "a_64bit"),
        other => panic!("expected _64bit counterexample, got {other:?}"),
    }

    // 32-bit fails (64 ok) → `_32bit` counterexample.
    match combine_dual_width_results(cex("a"), verified()) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert_eq!(obligation_name, "a_32bit"),
        other => panic!("expected _32bit counterexample, got {other:?}"),
    }

    // Both fail → `_32bit_64bit`, preferring the 32-bit witness.
    match combine_dual_width_results(cex("a"), cex("b")) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert_eq!(obligation_name, "a_32bit_64bit"),
        other => panic!("expected _32bit_64bit counterexample, got {other:?}"),
    }

    // 32-bit Unknown, 64-bit verified → fail-closed `_32bit` Unknown (not masked).
    match combine_dual_width_results(unknown(), verified()) {
        VerifyResult::Unknown { reason, .. } => assert!(reason.contains("arch_32bit")),
        other => panic!("32-bit Unknown must not be masked by 64-bit success, got {other:?}"),
    }

    // 32-bit Unknown, 64-bit counterexample → prefer the concrete witness, tag both.
    match combine_dual_width_results(unknown(), cex("b")) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert_eq!(obligation_name, "b_32bit_64bit"),
        other => panic!("expected the 64-bit counterexample preferred, got {other:?}"),
    }
}
// --------------------------------------------------------------------------
// Dual-arch `by(bit_vector)` discharge for pointer-width-polymorphic goals
// (#2778 cluster, upstream `bitvector.rs::test_double_arch_*`).
//
// A directive-free unit that mentions `usize`/`isize` is verified under a
// fixed 32-bit AND a fixed 64-bit pointer width (the dual-width path in
// `verify_unit_dual_width`). Under each *fixed* width the `by(bit_vector)`
// goal is a decidable QF-BV query, so the solver discharges it precisely:
// `usize::BITS` resolves to the pinned width, `usize`/`isize` parameters are
// the pinned-width bit-vector sort, and `as` casts between `usize` and `u32`
// are exact (zero-extend / truncate). A `Verified` verdict requires BOTH
// widths to discharge; otherwise the combined verdict is the failing one,
// tagged with the arch(es) on which the proof failed (`_32bit` / `_64bit` /
// `_32bit_64bit`) — the trust-vc analogue of upstream Verus's
// `assert_fails_bv_32bit` / `_64bit` / `_32bit_64bit`.
//
// These four cases mirror upstream `test_double_arch_ok`, `_fail32`,
// `_fail64`, and `_fail_both` byte-for-byte at the proof level (the same
// `usize::BITS`-guarded conjunction, the same `(c as usize) << 32 >> 32 == c`
// 64-bit fact, and the same `(a as u32) == (b as u32)` 32-bit fact). They lock
// in the should-VERIFY direction (the `_ok` conjunction) and all three
// should-FAIL arch classifications.

/// Builds a width-polymorphic `assert_by_bit_vector!` proof unit and verifies
/// it through the production dual-width source path.
fn verify_dual_arch_bv(name: &str, sig: &str, goal: &str) -> VerifyResult {
    let code = format!(
        "#[trust_vc::proof]\n\
         fn f({sig}) {{\n\
        \x20   trust_vc::assert_by_bit_vector!({goal});\n\
         }}\n"
    );
    let path = write_fixture(name, &code);
    verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run")
}

/// Upstream `test_double_arch_ok` (=> Ok). A conjunction whose two halves are
/// each guarded by `usize::BITS == N`: the 64-bit half (`((c as usize) << 32)
/// >> 32 == c`) is a theorem only when `usize` is 64-bit (and is vacuously
/// guarded away at 32-bit); the 32-bit half (`(a as u32) == (b as u32) ==> a ==
/// > > b`) is a theorem only when `usize` is 32-bit. Under each fixed width exactly
/// one half is active and holds, so the whole conjunction discharges at BOTH
/// widths and the combined dual-width verdict is `Verified`.
#[test]
fn dual_arch_bv_double_arch_ok_verifies_at_both_widths() {
    let result = verify_dual_arch_bv(
        "double_arch_ok.rs",
        "a: usize, b: usize, c: u32",
        "(usize::BITS == 64 ==> (((c as usize) << 32) >> 32 == c)) \
         && (usize::BITS == 32 ==> ((a as u32) == (b as u32) ==> a == b))",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "the `usize::BITS`-guarded conjunction is a theorem at both 32-bit and \
         64-bit usize; the combined dual-width verdict must be Verified, got \
         {result:?}"
    );
}

/// Upstream `test_double_arch_fail32` (=> `assert_fails_bv_32bit`).
/// `((c as usize) << 32) >> 32 == c` zero-extends `c: u32` into `usize`, shifts
/// left then right by 32. At 64-bit usize the round trip recovers `c` (theorem);
/// at 32-bit usize the `<< 32` shifts every bit out, so the result is `0`, which
/// differs from a nonzero `c` — a 32-bit-only counterexample. The combined
/// verdict is tagged `_32bit` (and NOT `_32bit_64bit`).
#[test]
fn dual_arch_bv_double_arch_fail32_tags_32bit_only() {
    let result = verify_dual_arch_bv(
        "double_arch_fail32.rs",
        "c: u32",
        "((c as usize) << 32) >> 32 == c",
    );
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.ends_with("_32bit") && !obligation_name.ends_with("_32bit_64bit"),
            "the shift round-trip fails only at 32-bit usize; the obligation must \
             be tagged `_32bit` (not `_32bit_64bit`), got {obligation_name:?}"
        ),
        other => {
            panic!("`((c as usize) << 32) >> 32 == c` must be refuted at 32-bit, got {other:?}")
        }
    }
}

/// Upstream `test_double_arch_fail64` (=> `assert_fails_bv_64bit`).
/// `(a as u32) == (b as u32) ==> a == b` truncates two `usize` values to their
/// low 32 bits and asserts that equal low halves imply full equality. At 32-bit
/// usize the truncation is the identity, so the implication holds (theorem); at
/// 64-bit usize two values can share low 32 bits yet differ in the high half — a
/// 64-bit-only counterexample. The combined verdict is tagged `_64bit` only.
#[test]
fn dual_arch_bv_double_arch_fail64_tags_64bit_only() {
    let result = verify_dual_arch_bv(
        "double_arch_fail64.rs",
        "a: usize, b: usize",
        "(a as u32) == (b as u32) ==> a == b",
    );
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.ends_with("_64bit") && !obligation_name.ends_with("_32bit_64bit"),
            "low-32-bit equality implies full equality only at 32-bit usize; the \
             obligation must be tagged `_64bit` (not `_32bit_64bit`), got \
             {obligation_name:?}"
        ),
        other => panic!("the implication must be refuted at 64-bit, got {other:?}"),
    }
}

/// Upstream `test_double_arch_fail_both` (=> `assert_fails_bv_32bit_64bit`).
/// `(a as u32) == (b as u32)` (unconditionally) is false for some `a`, `b` at
/// EVERY width (e.g. `a = 0`, `b = 1`), so both the 32-bit and the 64-bit pass
/// produce a counterexample and the combined verdict is tagged `_32bit_64bit`.
#[test]
fn dual_arch_bv_double_arch_fail_both_tags_both_archs() {
    let result = verify_dual_arch_bv(
        "double_arch_fail_both.rs",
        "a: usize, b: usize",
        "(a as u32) == (b as u32)",
    );
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            obligation_name.ends_with("_32bit_64bit"),
            "`(a as u32) == (b as u32)` is false for some inputs at both widths; \
             the obligation must be tagged `_32bit_64bit`, got {obligation_name:?}"
        ),
        other => panic!("the equality must be refuted at both widths, got {other:?}"),
    }
}

// --------------------------------------------------------------------------
// Pinned-directive `by(bit_vector)` discharge — upstream
// `bitvector.rs::bit_vector_usize_as_32bit` / `bit_vector_usize_as_64bit`.
//
// These two upstream cases are the canonical pairing of a *pinned*
// `global size_of usize == N` directive with `by(bit_vector)` assertions: the
// directive fixes the `usize` width to exactly N bytes and each `by(bit_vector)`
// goal is then a decidable QF-BV query over that fixed-width sort. They differ
// from the *dual-width* `by(bit_vector)` cases above (which leave the directive
// off and verify at BOTH widths): here a single width is pinned, so the unit is
// verified exactly once and a width-specific fact has a single, definite verdict
// rather than an arch-combined one.
//
// The fixtures below drive each upstream `proof fn` body through the production
// source path (`verify_function_from_file`), which scans the directive, installs
// the pinned width via `PointerWidthGuard`, and verifies the `by(bit_vector)`
// goal under that width. They pin the exact verdict split upstream asserts:
//
//   fact                                 N=4 (32-bit)   N=8 (64-bit)
//   ----------------------------------   ------------   ------------
//   x & x == x                           Verified       Verified
//   (!x) as u64 == !(x as u64)           FAILS          Verified
//   ((1usize << 35) >> 34) == 2usize     FAILS          Verified
//   (y >> 32) == 0usize                  Verified       FAILS
//
// (Upstream `bit_vector_usize_as_32bit` => `assert_fails(err, 4)`: its test3/4
// (`!x as u64`), test6/7 (`shl35`) fail at 32-bit; `bit_vector_usize_as_64bit`
// => `assert_fails(err, 4)`: its test2/3/5/6 (`y >> 32`) fail at 64-bit.) Every
// row is reproduced with the matching verifier verdict, so promotion of these
// two upstream cases is faithful, not gamed.

/// Builds a pinned-width `assert_by_bit_vector!` proof unit and verifies it
/// through the production single-width source path (directive scanned, width
/// installed, `by(bit_vector)` goal discharged at that fixed width).
fn verify_pinned_bv(name: &str, size_of_bytes: u32, sig: &str, goal: &str) -> VerifyResult {
    let code = format!(
        "global size_of usize == {size_of_bytes};\n\
         #[trust_vc::proof]\n\
         fn f({sig}) {{\n\
        \x20   trust_vc::assert_by_bit_vector!({goal});\n\
         }}\n"
    );
    let path = write_fixture(name, &code);
    verify_function_from_file(path.to_str().unwrap(), "f").expect("verification should run")
}

/// SHOULD-VERIFY at both widths. `x & x == x` is a width-invariant bit-vector
/// tautology, so it discharges whether `usize` is pinned 32-bit (`== 4`) or
/// 64-bit (`== 8`). Mirrors upstream `bit_vector_usize_as_32bit::test1` and
/// `bit_vector_usize_as_64bit::test1` (both pass).
#[test]
fn pinned_bv_and_self_verifies_at_both_pinned_widths() {
    for bytes in [4u32, 8u32] {
        let result = verify_pinned_bv(
            &format!("pinned_bv_and_self_{bytes}.rs"),
            bytes,
            "x: usize",
            "(x & x) == x",
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "`x & x == x` by(bit_vector) is width-invariant and must verify under \
             pinned `== {bytes}`, got {result:?}"
        );
    }
}

/// SHOULD-VERIFY, pinned 32-bit (`global size_of usize == 4`). When `usize` is
/// 32-bit, `(y >> 32)` shifts the entire value out, so `(y >> 32) == 0usize` is a
/// theorem. Mirrors upstream `bit_vector_usize_as_32bit::test5` (passes). The
/// 64-bit refutation below is its should-fail mirror, proving the directive — not
/// the host width — drove the verdict.
#[test]
fn pinned_bv_shr32_verifies_under_arch32() {
    let result = verify_pinned_bv("pinned_bv_shr32_arch32.rs", 4, "y: usize", "(y >> 32) == 0");
    assert!(
        matches!(result, VerifyResult::Verified),
        "under pinned `== 4`, `(y >> 32) == 0` by(bit_vector) shifts every bit out \
         and must verify, got {result:?}"
    );
}

/// SHOULD-FAIL, pinned 64-bit (`global size_of usize == 8`). The SAME
/// `(y >> 32) == 0usize` fact is refuted when `usize` is 64-bit: the high 32 bits
/// survive (witness `y = u64::MAX`), and the counterexample binding type is `u64`,
/// proving the pinned directive set the width. Single pinned width ⇒ no arch
/// suffix. Mirrors upstream `bit_vector_usize_as_64bit::test6` (`// FAILS`).
#[test]
fn pinned_bv_shr32_refutes_under_arch64() {
    let result = verify_pinned_bv("pinned_bv_shr32_arch64.rs", 8, "y: usize", "(y >> 32) == 0");
    match result {
        VerifyResult::Counterexample {
            obligation_name,
            bindings,
            ..
        } => {
            assert!(
                !obligation_name.ends_with("_32bit")
                    && !obligation_name.ends_with("_64bit")
                    && !obligation_name.ends_with("_32bit_64bit"),
                "a pinned-directive unit is single-width; the counterexample must \
                 carry no arch suffix, got {obligation_name:?}"
            );
            assert!(
                bindings.iter().any(|b| b.ty == "u64"),
                "`== 8` must make `usize` a 64-bit value (binding type `u64`), \
                 proving the directive set the bit-vector width, got {bindings:?}"
            );
        }
        other => panic!(
            "under pinned `== 8`, `(y >> 32) == 0` keeps the high bits and must be \
             refuted, got {other:?}"
        ),
    }
}

/// SHOULD-VERIFY, pinned 64-bit (`global size_of usize == 8`).
/// `(!x) as u64 == !(x as u64)` holds when `usize` is 64-bit: complement-then-cast
/// equals cast-then-complement because the cast is the identity at equal widths.
/// Mirrors upstream `bit_vector_usize_as_64bit::test4` (passes).
#[test]
fn pinned_bv_not_cast_verifies_under_arch64() {
    let result = verify_pinned_bv(
        "pinned_bv_not_cast_arch64.rs",
        8,
        "x: usize",
        "((!x) as u64) == (!(x as u64))",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "under pinned `== 8`, `(!x) as u64 == !(x as u64)` by(bit_vector) is a \
         theorem (identity cast) and must verify, got {result:?}"
    );
}

/// SHOULD-FAIL, pinned 32-bit (`global size_of usize == 4`). The SAME
/// `(!x) as u64 == !(x as u64)` is refuted when `usize` is 32-bit: `!x` complements
/// 32 bits then zero-extends to u64, whereas `!(x as u64)` complements all 64 bits,
/// so the high 32 bits differ. The counterexample binding type is `u32`. Single
/// pinned width ⇒ no arch suffix. Mirrors upstream
/// `bit_vector_usize_as_32bit::test4` (`// FAILS`).
#[test]
fn pinned_bv_not_cast_refutes_under_arch32() {
    let result = verify_pinned_bv(
        "pinned_bv_not_cast_arch32.rs",
        4,
        "x: usize",
        "((!x) as u64) == (!(x as u64))",
    );
    match result {
        VerifyResult::Counterexample {
            obligation_name,
            bindings,
            ..
        } => {
            assert!(
                !obligation_name.ends_with("_32bit")
                    && !obligation_name.ends_with("_64bit")
                    && !obligation_name.ends_with("_32bit_64bit"),
                "a pinned-directive unit is single-width; the counterexample must \
                 carry no arch suffix, got {obligation_name:?}"
            );
            assert!(
                bindings.iter().any(|b| b.ty == "u32"),
                "`== 4` must make `usize` a 32-bit value (binding type `u32`), \
                 proving the directive set the bit-vector width, got {bindings:?}"
            );
        }
        other => panic!(
            "under pinned `== 4`, `(!x) as u64 == !(x as u64)` differs in the high \
             32 bits and must be refuted, got {other:?}"
        ),
    }
}

/// SHOULD-VERIFY, pinned 64-bit (`global size_of usize == 8`).
/// `((1usize << 35) >> 34) == 2usize` holds when `usize` is 64-bit: `1 << 35` is in
/// range (35 < 64) and `>> 34` leaves `2`. Mirrors upstream
/// `bit_vector_usize_as_64bit::test7` (passes).
#[test]
fn pinned_bv_shl35_shr34_verifies_under_arch64() {
    let result = verify_pinned_bv(
        "pinned_bv_shl35_arch64.rs",
        8,
        "x: usize",
        "((1usize << 35) >> 34) == 2",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "under pinned `== 8`, `((1usize << 35) >> 34) == 2` by(bit_vector) is a \
         theorem (35 < 64) and must verify, got {result:?}"
    );
}

/// SHOULD-FAIL, pinned 32-bit (`global size_of usize == 4`). The SAME
/// `((1usize << 35) >> 34) == 2usize` is refuted when `usize` is 32-bit: `1 << 35`
/// shifts past the 32-bit width so the value is `0`, and `0 >> 34 == 0 != 2`.
/// Single pinned width ⇒ no arch suffix. Mirrors upstream
/// `bit_vector_usize_as_32bit::test7` (`// FAILS`).
#[test]
fn pinned_bv_shl35_shr34_refutes_under_arch32() {
    let result = verify_pinned_bv(
        "pinned_bv_shl35_arch32.rs",
        4,
        "x: usize",
        "((1usize << 35) >> 34) == 2",
    );
    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => assert!(
            !obligation_name.ends_with("_32bit")
                && !obligation_name.ends_with("_64bit")
                && !obligation_name.ends_with("_32bit_64bit"),
            "a pinned-directive unit is single-width; the counterexample must carry \
             no arch suffix, got {obligation_name:?}"
        ),
        other => panic!(
            "under pinned `== 4`, `((1usize << 35) >> 34) == 2` overshifts to 0 and \
             must be refuted, got {other:?}"
        ),
    }
}

/// CROSS-WIDTH DISCRIMINATOR for the pinned-directive `by(bit_vector)` path:
/// `(y >> 32) == 0` flips verdict purely with the directive — Verified at `== 4`,
/// refuted at `== 8` — and `((1usize << 35) >> 34) == 2` flips the other way. That
/// the verdict tracks the *pinned* width (not the host width, which is fixed for
/// the test run) is what proves the directive genuinely re-installs the
/// bit-vector width rather than the result being a host-width coincidence. This is
/// the pinned-`by(bit_vector)` analogue of
/// `cross_width_same_shift_amount_flips_verdict_with_directive`.
#[test]
fn pinned_bv_cross_width_directive_flips_verdict() {
    let shr32_32 = verify_pinned_bv("xw_shr32_32.rs", 4, "y: usize", "(y >> 32) == 0");
    let shr32_64 = verify_pinned_bv("xw_shr32_64.rs", 8, "y: usize", "(y >> 32) == 0");
    assert!(
        matches!(shr32_32, VerifyResult::Verified),
        "`(y >> 32) == 0` must verify at pinned 32-bit, got {shr32_32:?}"
    );
    assert!(
        matches!(shr32_64, VerifyResult::Counterexample { .. }),
        "the SAME `(y >> 32) == 0` must be refuted at pinned 64-bit — the directive \
         moved the width, got {shr32_64:?}"
    );

    let shl35_32 = verify_pinned_bv(
        "xw_shl35_32.rs",
        4,
        "x: usize",
        "((1usize << 35) >> 34) == 2",
    );
    let shl35_64 = verify_pinned_bv(
        "xw_shl35_64.rs",
        8,
        "x: usize",
        "((1usize << 35) >> 34) == 2",
    );
    assert!(
        matches!(shl35_32, VerifyResult::Counterexample { .. }),
        "`((1usize << 35) >> 34) == 2` must be refuted at pinned 32-bit (overshift), \
         got {shl35_32:?}"
    );
    assert!(
        matches!(shl35_64, VerifyResult::Verified),
        "the SAME `((1usize << 35) >> 34) == 2` must verify at pinned 64-bit — the \
         directive moved the width, got {shl35_64:?}"
    );
}
