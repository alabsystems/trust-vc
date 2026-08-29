// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Spec functions whose parameter is a user struct with a SHORT (1-2 uppercase
//! letter) name, plus the generic-shadowing control that pins the narrowness of
//! the fix.
//!
//! The flat type-string parser classifies a 1-2 uppercase-letter type name as a
//! generic `TypeParam` by convention, which erases to the uninterpreted `Poly`
//! sort. A user struct named `SP` therefore never reached the struct registry,
//! so the spec fn's body axiom bound its quantified variable at `Poly` while the
//! verified caller applied the same helper at the concrete datatype carrier.

pub struct SP {
    pub a: u64,
}

pub struct Catalog {
    pub a: u64,
}

#[trust_vc::spec]
fn inv_short(s: SP) -> bool {
    s.a > 10
}

#[trust_vc::spec]
fn inv_short_ref(s: &SP) -> bool {
    s.a > 10
}

#[trust_vc::spec]
fn inv_long(s: Catalog) -> bool {
    s.a > 10
}

// ---- TRUTH: entailed by the spec fn's body --------------------------------

#[trust_vc::requires(inv_short(p))]
#[trust_vc::ensures(result > 5)]
fn short_name_struct_param_truth(p: SP) -> u64 {
    p.a
}

#[trust_vc::requires(inv_short_ref(&p))]
#[trust_vc::ensures(result > 5)]
fn short_name_struct_param_by_ref_truth(p: SP) -> u64 {
    p.a
}

// LONG-NAME CONTROL: the same shape with a name the parser never mistakes for a
// type parameter. This path already worked and must be untouched by the fix.
#[trust_vc::requires(inv_long(p))]
#[trust_vc::ensures(result > 5)]
fn long_name_struct_param_truth(p: Catalog) -> u64 {
    p.a
}

// ---- LIARS: NOT entailed — `a > 10` gives `a >= 11`, never `a > 11` --------

#[trust_vc::requires(inv_short(p))]
#[trust_vc::ensures(result > 11)]
fn short_name_struct_param_liar(p: SP) -> u64 {
    p.a
}

#[trust_vc::requires(inv_short_ref(&p))]
#[trust_vc::ensures(result > 11)]
fn short_name_struct_param_by_ref_liar(p: SP) -> u64 {
    p.a
}

#[trust_vc::requires(inv_long(p))]
#[trust_vc::ensures(result > 11)]
fn long_name_struct_param_liar(p: Catalog) -> u64 {
    p.a
}
