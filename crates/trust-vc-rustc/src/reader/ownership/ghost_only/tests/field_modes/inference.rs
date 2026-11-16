// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Inferred value modes require original compiler facts, not ownership grants.

use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::{CheckKind, FnVcs};

mod compiler;
mod failures;

fn function<'a>(tcx: TyCtxt<'_>, read: &'a CrateRead, name: &str) -> &'a trust_vc_vcir::FnDecl {
    let owner = named(tcx, name);
    let found: Vec<_> = read
        .krate
        .fns
        .iter()
        .filter(|function| read.fn_defs.get(&function.id) == Some(&owner))
        .collect();
    assert_eq!(found.len(), 1, "{name}");
    found[0]
}

fn inferred_mode(tcx: TyCtxt<'_>, read: &CrateRead, name: &str, expected: Mode) {
    let owner = named(tcx, name);
    let pattern = binding(tcx, owner, "inferred");
    let facts = checked(tcx, name);
    let body = tcx.hir_body_owned_by(owner);
    assert_eq!(
        facts
            .bindings
            .mode_for(tcx, owner, owner, body, pattern)
            .unwrap(),
        expected
    );
    let local: Vec<_> = function(tcx, read, name)
        .locals
        .iter()
        .filter(|local| local.name == "inferred" && read.span(local.span) == Some(pattern.span))
        .collect();
    assert_eq!(local.len(), 1, "{name}");
    assert_eq!(local[0].kind, LocalKind::Let);
    assert_eq!(local[0].mode, expected);
}

// The outer architecture batch carries an unused literal sentinel. Require
// actual nonliteral scalar goals in both complete semantic contexts instead.
fn nonliteral_architecture_goals(name: &str, query: &trust_vc_vcir::vcgen::Query) {
    let Some([(32, first), (64, second)]) = query.architectures.as_deref() else {
        panic!("{name}: expected the complete ordered 32/64 batch: {query:#?}");
    };
    assert!(query.bitvector.is_none(), "{name}: {query:#?}");
    for (width, child) in [(32, first), (64, second)] {
        assert!(
            child.architectures.is_none() && child.bitvector.is_none(),
            "{name}/{width}: expected an ordinary scalar leaf: {child:#?}"
        );
        assert!(
            !matches!(child.goal, trust_vc_vcir::vcgen::term::Term::Bool(_)),
            "{name}/{width}: expected a nonliteral semantic goal: {child:#?}"
        );
    }
}

#[test]
fn native_inferred_exec_and_spec_values_reach_original_bodies_and_real_queries() {
    native(
        r#"
#[verus::internal(verus_macro)]
fn Initialized(value: u64) -> u64 { let initialized = value; initialized }
#[verus::internal(verus_macro)]
fn ExecLate(value: u64) -> u64 { #[verus::internal(infer_mode)] let inferred; inferred = value; inferred }
#[verus::internal(verus_macro)]
fn SpecLate(value: u64) {
    #[verus::internal(infer_mode)] let inferred;
    #[verifier::proof_block] { let ghost = value; inferred = ghost; let observed = inferred; }
}
#[verus::internal(verus_macro)]
fn ExecBranchGood(flag: bool, first: u64, second: u64) {
    #[verus::internal(infer_mode)] let inferred;
    if flag { inferred = first; } else { inferred = second; }
    #[verifier::proof_block] { ghost_value_builtin_fixture::assert_(if flag { inferred == first } else { inferred == second }); }
}
#[verus::internal(verus_macro)]
fn ExecBranchBad(flag: bool, first: u64, second: u64) {
    #[verus::internal(infer_mode)] let inferred;
    if flag { inferred = first; } else { inferred = second; }
    #[verifier::proof_block] { ghost_value_builtin_fixture::assert_(if flag { inferred != first } else { inferred != second }); }
}
#[verus::internal(verus_macro)]
fn SpecBranchGood(flag: bool, first: u64, second: u64) {
    #[verus::internal(infer_mode)] let inferred;
    #[verifier::proof_block] {
        let ghost_flag = flag; let ghost_first = first; let ghost_second = second;
        if ghost_flag { inferred = ghost_first; } else { inferred = ghost_second; }
        ghost_value_builtin_fixture::assert_(if ghost_flag { inferred == ghost_first } else { inferred == ghost_second });
    }
}
#[verus::internal(verus_macro)]
fn SpecBranchBad(flag: bool, first: u64, second: u64) {
    #[verus::internal(infer_mode)] let inferred;
    #[verifier::proof_block] {
        let ghost_flag = flag; let ghost_first = first; let ghost_second = second;
        if ghost_flag { inferred = ghost_first; } else { inferred = ghost_second; }
        ghost_value_builtin_fixture::assert_(if ghost_flag { inferred != ghost_first } else { inferred != ghost_second });
    }
}
"#,
        |tcx, read| {
            assert!(read.errors.is_empty(), "{:?}", read.errors);
            assert!(
                read.refusals().next().is_none(),
                "{:?}",
                read.refusals().collect::<Vec<_>>()
            );
            assert!(
                read.verify_refusals.is_empty(),
                "{:?}",
                read.verify_refusals
            );
            let errors = trust_vc_vcir::wf::check_crate(&read.krate);
            assert!(errors.is_empty(), "{errors:?}");
            assert_eq!(read.krate.fns.len(), 7);
            for name in ["ExecLate", "ExecBranchGood", "ExecBranchBad"] {
                inferred_mode(tcx, read, name, Mode::Exec);
            }
            for name in ["SpecLate", "SpecBranchGood", "SpecBranchBad"] {
                inferred_mode(tcx, read, name, Mode::Spec);
            }
            let generated = trust_vc_vcir::vcgen::generate(&read.krate);
            for name in [
                "Initialized",
                "ExecLate",
                "SpecLate",
                "ExecBranchGood",
                "ExecBranchBad",
                "SpecBranchGood",
                "SpecBranchBad",
            ] {
                let declaration = function(tcx, read, name);
                assert_eq!(declaration.role, trust_vc_vcir::FnRole::Item);
                assert!(!declaration.attrs.external_body && declaration.attrs.instance.is_none());
                let Some(FnVcs::Checks(checks)) = generated.get(declaration.id) else {
                    panic!("{name}: {generated:?}");
                };
                let goal = match name {
                    "ExecBranchGood" | "SpecBranchGood" => Some(true),
                    "ExecBranchBad" | "SpecBranchBad" => Some(false),
                    _ => None,
                };
                assert_eq!(
                    checks.len(),
                    usize::from(goal.is_some()),
                    "{name}: {checks:?}"
                );
                if let Some(proved) = goal {
                    assert!(matches!(checks[0].kind, CheckKind::Assert { .. }));
                    assert!(!checks[0].approximate && !checks[0].order_unknown);
                    nonliteral_architecture_goals(name, &checks[0].query);
                    let answer = check_detailed(
                        &checks[0].query,
                        "native inferred values",
                        &Limits::default(),
                    );
                    assert!(
                        matches!(
                            (&answer.verdict, proved),
                            (Verdict::Proved { .. }, true) | (Verdict::Refuted { .. }, false)
                        ),
                        "{name}: {answer:?}"
                    );
                }
            }
            assert!(read.native_ownership.is_empty());
        },
        false,
    );
}
