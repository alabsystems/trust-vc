// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Reproducer + narrowness pins for trait-method contract selection under a
//! COLLIDING bare method name.
//!
//! `dual_named_method` is declared by TWO `#[trust_vc::trait_spec]` traits with
//! CONFLICTING `returns`. A caller generic over `T: SpecNine` must inherit
//! SpecNine's postcondition and a caller generic over `T: SpecTwo` must inherit
//! SpecTwo's — selection is keyed by the BOUND, never by the bare method name.
//!
//! Ground truth under stock `rustc --edition 2021` (same shape, attributes
//! stripped): `first_bound(HolderNine) == 9`, `second_bound(HolderTwo) == 2`,
//! `sole_bound(HolderSole) == 7`. So in each pair below the `_verifies` claim is
//! the TRUE one and the `_must_not_verify` claim is FALSE.
//!
//! SpecNine is declared FIRST, so a bare-name first-declaration-wins registry
//! agrees with the correct answer on the SpecNine bound and disagrees only on
//! the SpecTwo bound — which is why the second-bound pair is the discriminator
//! and the first-bound pair alone would prove nothing.

#[trust_vc::trait_spec]
trait SpecNine {
    #[trust_vc::returns(9u8)]
    fn dual_named_method(&self) -> u8;
}

#[trust_vc::trait_spec]
trait SpecTwo {
    #[trust_vc::returns(2u8)]
    fn dual_named_method(&self) -> u8;
}

#[trust_vc::trait_spec]
trait SoleSpec {
    #[trust_vc::returns(7u8)]
    fn sole_named_method(&self) -> u8;
}

struct HolderNine;
struct HolderTwo;
struct HolderSole;

#[trust_vc::external]
#[trust_vc::trait_impl]
impl SpecNine for HolderNine {
    fn dual_named_method(&self) -> u8 {
        9u8
    }
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl SpecTwo for HolderTwo {
    fn dual_named_method(&self) -> u8 {
        2u8
    }
}

#[trust_vc::external]
#[trust_vc::trait_impl]
impl SoleSpec for HolderSole {
    fn sole_named_method(&self) -> u8 {
        7u8
    }
}

// ---- bound = the FIRST-declared colliding trait ----

/// TRUE: `SpecNine::dual_named_method` returns 9.
#[trust_vc::ensures(true)]
fn first_bound_true_claim_verifies<T: SpecNine>(v: &T) {
    let r = v.dual_named_method();
    trust_vc::assert!(r == 9u8);
}

/// FALSE: 2 is SpecTwo's postcondition, not SpecNine's.
#[trust_vc::ensures(true)]
fn first_bound_false_claim_must_not_verify<T: SpecNine>(v: &T) {
    let r = v.dual_named_method();
    trust_vc::assert!(r == 2u8);
}

// ---- bound = the SECOND-declared colliding trait (ORDER-FLIP discriminator) ----

/// TRUE: `SpecTwo::dual_named_method` returns 2.
#[trust_vc::ensures(true)]
fn second_bound_true_claim_verifies<T: SpecTwo>(v: &T) {
    let r = v.dual_named_method();
    trust_vc::assert!(r == 2u8);
}

/// FALSE: 9 is SpecNine's postcondition, reachable only by resolving the bound
/// through the bare method name.
#[trust_vc::ensures(true)]
fn second_bound_false_claim_must_not_verify<T: SpecTwo>(v: &T) {
    let r = v.dual_named_method();
    trust_vc::assert!(r == 9u8);
}

// ---- NARROWNESS PIN: a NON-colliding method name must still resolve ----

/// TRUE: `SoleSpec::sole_named_method` returns 7. Pins that collision handling
/// does not degenerate into declining every trait-bound postcondition.
#[trust_vc::ensures(true)]
fn sole_bound_true_claim_verifies<T: SoleSpec>(v: &T) {
    let r = v.sole_named_method();
    trust_vc::assert!(r == 7u8);
}

/// FALSE: the uncollided bound must still REFUTE a wrong value, so the pin above
/// cannot be satisfied by an inconsistent (everything-provable) context.
#[trust_vc::ensures(true)]
fn sole_bound_false_claim_must_not_verify<T: SoleSpec>(v: &T) {
    let r = v.sole_named_method();
    trust_vc::assert!(r == 9u8);
}
