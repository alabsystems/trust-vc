// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! COMPLETENESS PIN (trait rows / pruning, 2026-09-11): a goal that names no
//! trait is not left `Unknown` under the file's trait axioms. The batch-wide
//! shared bit-vector encoder is built without a focus and carries every trait
//! of the file (each a quantified postcondition axiom over the `Poly` self
//! sort); when the solver answers `Unknown` there, the goal now falls back to
//! the focused per-assertion lane, whose plan prunes the traits the goal
//! cannot reach. Before, a plain false postcondition beside a handful of
//! traits came back solver `Unknown (quantifier-unhandled)` instead of a
//! model-bearing Counterexample (upstream returns_postcondition
//! `returns_basic_wrong_value`). Goals that DO name a trait keep their axioms.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_tap_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
// LIAR: a plain false postcondition, unrelated to every trait below — must
// refute with a model, not drown in quantified axioms.
#[trust_vc::ensures(result == 20u8)]
fn wrong_value() -> u8 {
    19u8
}

// CONTROL: the matching claim verifies.
#[trust_vc::ensures(result == 19u8)]
fn right_value() -> u8 {
    19u8
}

// CONTROL: a goal that names a trait keeps its axioms (the contract of the
// default method is what the caller sees).
#[trust_vc::ensures(true)]
fn uses_trait_contract<T: DefaultTrue>(value: T) {
    let returned = value.default_true();
    trust_vc::assert!(returned);
}

// LIAR: … and the contract is not stronger than written.
#[trust_vc::ensures(true)]
fn uses_trait_contract_liar<T: DefaultTrue>(value: T) {
    let returned = value.default_true();
    trust_vc::assert!(!returned);
}

#[trust_vc::trait_spec]
trait DefaultTrue {
    #[trust_vc::ensures(result == true)]
    fn default_true(self) -> bool {
        true
    }
}
#[trust_vc::trait_impl]
impl DefaultTrue for bool {}

#[trust_vc::trait_spec]
trait DefaultInput {
    #[trust_vc::contract(ensures(result == input), returns(result))]
    fn default_input(input: u8) -> u8 {
        input
    }
}
#[trust_vc::trait_impl]
impl DefaultInput for bool {}

#[trust_vc::trait_spec]
trait Mismatch {
    #[trust_vc::returns(true)]
    fn default_false() -> bool {
        false
    }
}
#[trust_vc::trait_impl]
impl Mismatch for bool {}

#[trust_vc::trait_spec]
trait AbstractTrue {
    #[trust_vc::ensures(result == true)]
    fn abstract_true() -> bool;
}
#[trust_vc::trait_impl]
impl AbstractTrue for bool {
    fn abstract_true() -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait AbstractInput {
    #[trust_vc::ensures(result == input)]
    fn abstract_input(input: u8) -> u8;
}
#[trust_vc::trait_impl]
impl AbstractInput for bool {
    fn abstract_input(input: u8) -> u8 {
        input
    }
}
"#;

#[test]
fn liar_beside_many_traits_refutes_with_a_model() {
    match verify("l1", "wrong_value", SRC) {
        VerifyResult::Counterexample { model, .. } => {
            assert!(model.is_some(), "the refutation must carry a model");
        }
        other => panic!("wrong_value: expected a model-bearing Counterexample, got {other:?}"),
    }
}

#[test]
fn control_beside_many_traits_verifies() {
    match verify("c1", "right_value", SRC) {
        VerifyResult::Verified => {}
        other => panic!("right_value: expected Verified, got {other:?}"),
    }
}

#[test]
fn control_trait_goal_keeps_its_axioms() {
    match verify("c2", "uses_trait_contract", SRC) {
        VerifyResult::Verified => {}
        other => panic!("uses_trait_contract: expected Verified, got {other:?}"),
    }
}

#[test]
fn liar_trait_goal_is_rejected() {
    match verify("l2", "uses_trait_contract_liar", SRC) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("uses_trait_contract_liar: expected Counterexample, got {other:?}"),
    }
}
