// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ENGINE SEAM: a `state_machine!`-generated definition whose body axiom the
//! engine would DROP must be a hard error, never a silently uninterpreted
//! function — an uninterpreted relation would make the generated lemma
//! contracts meaningless while still reporting `Verified`.
//!
//! The items here are hand-written in the shape the expander emits (carrying
//! the generated-item doc marker) and then pushed into each axiom-dropping
//! path on purpose. This file declares no `state_machine!` invocation, so the
//! expander is an exact no-op over it.

#![allow(dead_code, unused_variables, non_camel_case_types, non_snake_case)]

use trust_vc_types::int;

#[doc = "trust_vc:state_machine_generated"]
pub struct __TvcSm_Seam_State {
    pub z: int,
}

impl __TvcSm_Seam_State {
    /// A body the inherent-method lane cannot reduce to a single return
    /// expression: its definitional axiom is dropped.
    #[doc = "trust_vc:state_machine_generated"]
    #[trust_vc::spec]
    pub fn invariant(&self) -> bool {
        if self.z > 0 {
            return true;
        }
        false
    }
}

/// An opaque generated relation: the catalog would publish no body axiom.
#[doc = "trust_vc:state_machine_generated"]
#[trust_vc::spec]
#[trust_vc::opaque]
pub fn __TvcSm_Seam__tr(pre: __TvcSm_Seam_State, post: __TvcSm_Seam_State) -> bool {
    post.z == pre.z + 1
}

#[trust_vc::proof]
#[trust_vc::requires(__TvcSm_Seam__tr(pre, post))]
#[trust_vc::ensures(post.z == pre.z + 1)]
fn seam_relation_axiom_dropped(pre: __TvcSm_Seam_State, post: __TvcSm_Seam_State) {}

#[trust_vc::proof]
#[trust_vc::requires(pre.invariant())]
#[trust_vc::ensures(pre.z > 0)]
fn seam_invariant_axiom_dropped(pre: __TvcSm_Seam_State) {}

/// An ordinary (unmarked) function in the same file still verifies.
#[trust_vc::proof]
#[trust_vc::requires(a >= 1)]
#[trust_vc::ensures(a + 1 >= 2)]
fn seam_unmarked_control(a: int) {}
