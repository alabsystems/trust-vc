// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CARDINAL fail-closed pins for the ENCODE-THEN-CLOSE BINDER-CAPTURE **class**.
//!
//! `tests/data/hoist_capture_class.rs` carries the mechanism. In one line: an
//! axiom body is encoded before its `forall` is built, so any helper that
//! hoists a fresh const's defining equation to the solver top level during that
//! encode has the equation left OUTSIDE the binder while the const it returned
//! sits INSIDE — and the axiom degenerates to "`f` is a constant function".
//!
//! Scope of the class, enumerated not guessed: **47 helpers on
//! `AstExpressionParser`** mint a fresh const and reach a `try_assert_term` in
//! the same function; 9 of them assert at the top level with no gate at all.
//! Three were measured on pristine `trust-vc 7eb96392`:
//!
//! | site | probe | pristine |
//! |---|---|---|
//! | `bind_datatype_match_result` | `forall\|c,d\| next(c) == next(d)` | VERIFIED (FALSE) |
//! | `purified_euclidean_div_mod_literal` | `half(2) == 5` | VERIFIED (FALSE) |
//! | `reinterpret_bv_signedness` | `sflip(0) == sflip(1)` | VERIFIED (FALSE) |
//!
//! Sites 1 and 2 are closed by INLINING. Every other hoisting HELPER —
//! enumerated or not, present or added later — is closed by the general
//! backstop in `encoder::binder_capture`, which declines the axiom outright at
//! each WIRED closure boundary (spec-fn fuel axioms, the four trait-axiom
//! emitters, broadcast lemmas, the datatype-invariant axiom, the `choose`
//! Skolem axiom). A NEW closure boundary must wire the watermark itself — the
//! module doc carries the checklist. Site 3 is the measured instance of the
//! decline path.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/hoist_capture_class.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn ok(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|e| panic!("extract/verify {func} failed: {e:?}"))
}

/// CARDINAL. Every one of these goals is FALSE. A `Verified` on any of them
/// means a hoist made during the body encode was captured by the defining
/// axiom's `forall`, collapsing the spec fn to a constant — or, for the
/// Euclidean site, making the whole axiom set contradictory.
#[test]
fn captured_hoists_do_not_collapse_a_spec_fn_to_a_constant() {
    let false_goals = [
        // site 1 — datatype-valued match (closed by inlining)
        "f_match_forall_constant",
        "f_match_red_neq_green",
        // site 2 — Euclidean div/mod (closed by inlining)
        "f_euclid_two_is_five",
        "f_euclid_zero_two",
        "f_euclid_forall_constant",
        "f_parity_zero_one",
        // site 3 — signedness cast (closed by the general backstop)
        "f_cast_zero_one",
        "f_cast_forall_constant",
        // site 4 — the `choose` Skolem-witness boundary (wired with the same
        // watermark + flag; measured Counterexample in 0.01s on the wired arm)
        "f_choose_unsat_nat",
        "f_choose_sat_consistency",
        // isolation control: no hoisting helper, must never verify in any arm
        "f_clean_collapse",
    ];
    let mut verified = Vec::new();
    for func in false_goals {
        let result = ok(func);
        if matches!(result, VerifyResult::Verified) {
            verified.push(func);
        }
    }
    assert!(
        verified.is_empty(),
        "CARDINAL FALSE VERIFY — a captured top-level hoist collapsed the spec-fn \
         defining axiom for: {verified:?}"
    );
}

/// NO-OVER-REJECTION. The fix must not be "drop the definition": every TRUE
/// goal here needs the spec fn's meaning, including the three SYMBOLIC ones
/// that no ground replay can decide by evaluation alone.
///
/// `t_cast_*` are in this list deliberately. Site 3's defining axiom IS
/// declined, and these still verify — measured, not assumed — because the
/// ground-pool replay re-encodes the body per concrete instance and therefore
/// cannot be captured. That is what makes the backstop fail-CLOSED rather than
/// fail-useless.
#[test]
fn the_fix_keeps_every_definition_that_was_provable_before() {
    for func in [
        "t_match_red_is_green",
        "t_match_symbolic",
        "t_match_forall_not_red",
        "t_euclid_two_is_one",
        "t_euclid_symbolic",
        "t_euclid_forall_bound",
        "t_parity_one_is_one",
        "t_cast_one_is_one",
        "t_cast_symbolic",
        "t_cast_nonneg",
        "t_clean_one_is_two",
        "t_clean_symbolic",
    ] {
        let result = ok(func);
        assert!(
            matches!(result, VerifyResult::Verified),
            "TRUE goal {func} must still Verify — the binder-capture fix must keep \
             the definition usable, not delete it; got {result:?}"
        );
    }
}

/// Ad-hoc probe runner, asserts nothing: set `TRUST_VC_HOIST_PROBE` to a
/// comma-separated list of fixture functions and run with `--nocapture` to
/// print each verdict. This is the measurement instrument the SITE 4 pins
/// were derived with (run on the patched and the pristine arm and diff).
#[test]
fn probe_runner() {
    let Ok(funcs) = std::env::var("TRUST_VC_HOIST_PROBE") else {
        return;
    };
    for func in funcs.split(',').filter(|f| !f.is_empty()) {
        let started = std::time::Instant::now();
        let result = verify_function_from_file(&path(), func);
        eprintln!(
            "PROBE\t{func}\t{:?}\t{:.2}s",
            result,
            started.elapsed().as_secs_f64()
        );
    }
}

/// Child process helper for the known-open pin below. Inert unless the parent
/// sets `TRUST_VC_HOIST_PIN_CHILD`, so it costs nothing in a normal run.
#[test]
fn hoist_trace_child_helper() {
    if std::env::var_os("TRUST_VC_HOIST_PIN_CHILD").is_none() {
        return;
    }
    let _ = ok("t_cast_nonneg");
}

/// KNOWN-OPEN, deliberately pinned rather than left silent.
///
/// `cast.rs::reinterpret_bv_signedness` is closed FAIL-CLOSED, not repaired:
/// the backstop declines `sflip`'s whole defining axiom instead of the helper
/// inlining its cast the way `match_encode.rs` and `arith/int_arith.rs` now do.
/// No verdict regression was measured (see
/// `the_fix_keeps_every_definition_that_was_provable_before`), so a verdict
/// cannot express what is still open — this test asserts on the DECLINE ITSELF,
/// by re-running one verification in a child process with the
/// `TRUST_VC_BINDER_CAPTURE_TRACE` trace enabled and requiring that no axiom
/// was declined for `sflip`.
///
/// TO CLOSE: in `reinterpret_bv_signedness`, register the inner term with the
/// cast's SOURCE signedness (or bind through a scope-aware alias) so the
/// non-hoisting branch stops reporting
/// `sort metadata mismatch: IR declared Uint{32}, tracked width=32 signed=true`,
/// gate its hoist on `pending_universal_closure` as `int_arith.rs` does, then
/// delete this `#[ignore]`.
#[test]
#[ignore = "KNOWN-OPEN: the signedness-cast hoist is closed by DECLINING the \
            defining axiom rather than by inlining. Sound, but not repaired."]
fn known_open_signedness_cast_hoist_is_declined_not_inlined() {
    let exe = std::env::current_exe().expect("current_exe");
    let out = std::process::Command::new(exe)
        .args(["--exact", "hoist_trace_child_helper", "--nocapture"])
        .env("TRUST_VC_HOIST_PIN_CHILD", "1")
        .env("TRUST_VC_BINDER_CAPTURE_TRACE", "1")
        .output()
        .expect("spawn child test process");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let declined: Vec<&str> = stderr
        .lines()
        .filter(|l| l.contains("TRUST_VC_BINDER_CAPTURE") && l.contains("sflip"))
        .collect();
    assert!(
        declined.is_empty(),
        "the `sflip` defining axiom is still DECLINED rather than encoded \
         capture-free — inline `reinterpret_bv_signedness` instead. Trace: {declined:?}"
    );
}
