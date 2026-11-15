// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `with_limits()` installs ONE envelope, and it covers certification.
//!
//! ay keeps two deadline cells, and only one public control moves both.
//! `Executor::set_solve_controls` (ay `executor/check_sat.rs:2949-2958`)
//! copies the caller's `set_timeout` into `solve_deadline` AND
//! `certification_deadline`, while `install_quantifier_deadline_backstop`
//! (`check_sat.rs:3125-3172`) widens `solve_deadline` alone. A caller that
//! opts in to that widener buys search time it cannot publish: after the
//! search, `restore_timeout_deadline_after_call` hands the expired nominal
//! back, `certify_unsat_for_publication` refuses the computed UNSAT on an
//! expired certification envelope, and
//! `decline_definite_publication_on_external_stop` revokes any definite
//! verdict as `Unknown(Timeout)`.
//!
//! trust-vc was in exactly that state for one day (`71e19312`, 2026-09-15),
//! and the two realbody read-back controls went red 11 runs in 14 — 8 as
//! `Timeout`, 3 as `ConfirmationDisagree`, the two exit doors of that single
//! boundary. These tests pin the shape that has no boundary to fall off:
//! one wall, asked for once, honored by search and certification alike.
//!
//! See `verification::timeout::DEFAULT_SOLVER_WALL_BACKSTOP_MS` for the full
//! call chain and the measurement.

use super::*;
use crate::solver_budget::ConflictBudget;

/// The production envelope installs the wall it was given and does NOT opt in
/// to ay's search-only widener.
#[test]
fn with_limits_installs_one_envelope_for_search_and_certification() {
    let encoder = AYEncoder::new().with_limits(30_000, ConflictBudget::bounded(400_000), 512);
    assert_eq!(
        encoder.solver.timeout(),
        Some(std::time::Duration::from_millis(30_000)),
        "with_limits() must install the wall it was given"
    );
    assert!(
        !encoder.solver.quantifier_deadline_backstop(),
        "with_limits() must NOT opt in to ay's quantified deadline backstop: it widens \
         `solve_deadline` only, so a solve that runs past the nominal is refused at \
         certification or revoked at publication. Ask for a bigger wall instead — \
         `set_timeout` moves both cells"
    );
}

/// A bare encoder carries no wall and no widener: the envelope is installed in
/// exactly one place.
#[test]
fn a_bare_encoder_installs_neither_wall_nor_widener() {
    let encoder = AYEncoder::new();
    assert_eq!(encoder.solver.timeout(), None);
    assert!(
        !encoder.solver.quantifier_deadline_backstop(),
        "ay's backstop is off by default (ay 6226726f3) and trust-vc keeps it off"
    );
}

/// The default wall is the envelope the withdrawn widener used to buy.
///
/// Dropping the opt-in without raising the wall would have cut the effective
/// quantified search budget from 120 s back to 30 s — a capability loss. This
/// test states the arithmetic so that the two halves cannot be separated: the
/// widener is gone BECAUSE the nominal now covers what it granted.
#[test]
fn default_wall_covers_what_the_withdrawn_widener_used_to_buy() {
    use std::time::Duration;
    const PREVIOUS_NOMINAL: Duration = Duration::from_secs(30);
    let widened = PREVIOUS_NOMINAL + (PREVIOUS_NOMINAL * 3).min(Duration::from_secs(180));
    let wall =
        Duration::from_millis(super::super::verification::timeout::DEFAULT_SOLVER_WALL_BACKSTOP_MS);
    assert_eq!(
        wall, widened,
        "the default wall must be at least what ay's widener used to extend the \
         30 s nominal to, or dropping the opt-in silently shrinks every quantified solve"
    );
}

/// The external hang watchdog sits just beyond the single envelope.
///
/// With no widener there is nothing to mirror: ay's deadline for a trust-vc
/// solve IS the nominal wall, so the watchdog is that wall plus the grace and
/// can only fire when ay has failed to honor its own deadline.
#[test]
fn far_out_watchdog_sits_just_beyond_the_single_envelope() {
    use std::time::Duration;
    let wall =
        Duration::from_millis(super::super::verification::timeout::DEFAULT_SOLVER_WALL_BACKSTOP_MS);
    let watchdog = super::super::verification::timeout::far_out_watchdog_timeout(None);
    assert!(
        watchdog > wall,
        "watchdog {watchdog:?} must sit beyond ay's own deadline {wall:?}"
    );
    assert_eq!(
        watchdog - wall,
        Duration::from_secs(10),
        "the watchdog is the wall plus the grace, nothing else — a larger gap means a \
         widener is being mirrored again"
    );
}

/// No seed is installed by default, and the option ay would need is accepted.
///
/// Two halves, because only one of them is observable. (1) The parse rule:
/// `TRUST_VC_AY_RANDOM_SEED` unset or unparsable means NO option — never
/// "seed 0", which is a different thing at the ay boundary (absent option vs
/// installed option). (2) ay accepts `random-seed` under both logics
/// `setup_from_prepared` builds encoders with, so a sweep that sets the
/// variable really is sweeping seeds rather than silently warning. ay exposes
/// no public getter for an option value, so the install itself cannot be read
/// back.
#[test]
fn no_seed_by_default_and_ay_accepts_one_when_asked() {
    use super::super::{configured_ay_random_seed, parse_ay_random_seed};
    assert_eq!(parse_ay_random_seed(""), None);
    assert_eq!(parse_ay_random_seed("not-a-seed"), None);
    assert_eq!(parse_ay_random_seed("0"), Some(0));
    assert_eq!(parse_ay_random_seed(" 42 "), Some(42));
    if std::env::var_os("TRUST_VC_AY_RANDOM_SEED").is_none() {
        assert_eq!(
            configured_ay_random_seed(),
            None,
            "with the variable unset, trust-vc must install no seed and leave ay on its own"
        );
    }
    for logic in [ay_dpll::api::Logic::All, ay_dpll::api::Logic::QfBv] {
        let mut encoder = AYEncoder::with_logic(logic);
        assert!(
            encoder.solver.try_set_option("random-seed", "7").is_ok(),
            "ay must accept `random-seed` on {logic:?}, or a seed sweep is measuring \
             nothing but its own warning"
        );
    }
}

fn second_parameter_query() -> (AYEncoder, ay_dpll::api::FuncDecl) {
    use ay_core::Sort;
    let mut encoder = AYEncoder::with_logic(ay_dpll::api::Logic::All).with_limits(
        30_000,
        ConflictBudget::bounded(400_000),
        512,
    );
    let solver = &mut encoder.solver;
    let function = solver
        .try_declare_fun("vc_second_parameter", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let x = solver.try_declare_const("x", Sort::Int).unwrap();
    let y = solver.try_declare_const("y", Sort::Int).unwrap();
    let application = solver.try_apply(&function, &[x, y]).unwrap();
    let greater = solver.try_gt(application, y).unwrap();
    let universal = solver.try_forall(&[x, y], greater).unwrap();
    solver.try_assert_term(universal).unwrap();
    (encoder, function)
}

#[test]
fn published_ay_certifies_second_parameter_models_at_the_consumer_boundary() {
    use ay_dpll::api::ModelValue;
    let (mut encoder, function) = second_parameter_query();
    let solver = &mut encoder.solver;
    let zero = solver.int_const(0);
    let three = solver.int_const(3);
    let four = solver.int_const(4);
    let point = solver.try_apply(&function, &[zero, three]).unwrap();
    let equality = solver.try_eq(point, four).unwrap();
    let exclusion = solver.try_not(equality).unwrap();
    solver.try_assert_term(exclusion).unwrap();
    assert!(
        solver.try_check_sat().unwrap().is_sat(),
        "{:?}",
        solver.unknown_reason()
    );
    assert!(solver.try_get_model_for_consumer().is_ok());
    let document = solver.try_get_model_str().unwrap();
    assert!(
        document.contains("vc_second_parameter") && document.contains("x!1"),
        "{document}"
    );
    for (first, second) in [(100, 10), (10, -100)] {
        let first = solver.int_const(first);
        let argument = solver.int_const(second);
        let application = solver.try_apply(&function, &[first, argument]).unwrap();
        let ModelValue::Int(value) = solver.try_get_value(application).unwrap() else {
            panic!("the certified Int function must retain its result sort");
        };
        assert!(value > second.into());
    }
    assert_ne!(
        solver.try_get_value(point).unwrap(),
        ModelValue::Int(4.into())
    );
}

#[test]
fn published_ay_refutes_the_original_second_parameter_contradiction() {
    let (mut encoder, function) = second_parameter_query();
    let solver = &mut encoder.solver;
    let zero = solver.int_const(0);
    let three = solver.int_const(3);
    let point = solver.try_apply(&function, &[zero, three]).unwrap();
    let greater = solver.try_gt(point, three).unwrap();
    let contradiction = solver.try_not(greater).unwrap();
    solver.try_assert_term(contradiction).unwrap();
    assert!(
        solver.try_check_sat().unwrap().is_unsat(),
        "{:?}",
        solver.unknown_reason()
    );
    assert!(solver.try_get_model().is_err());
}
