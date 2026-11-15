// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! COMPILE LANE: the `#[proc_macro] trust_vc::state_machine!` expansion has to
//! produce Rust that rustc accepts, with `NAME::State::…` paths resolving.
//!
//! This is a plain integration test, not a trybuild case: the machine below is
//! written at item position, so the test binary only builds if the expansion
//! compiles. Verification itself happens on the FILE lane (see
//! `state_machine_dsl_soundness.rs`); the compile lane adds the documented
//! shims (`pub mod NAME { pub use .. as State; }` plus associated wrappers)
//! that the file lane deliberately does not emit, because an alias and
//! wrappers would reintroduce the bare-name collisions the generated root
//! names exist to avoid.

#![allow(dead_code)]

use trust_vc_types::int;

trust_vc::state_machine! { Cl {
    fields {
        pub y: int,
        pub z: int,
    }

    init! {
        initialize(y: int, z: int) {
            require(y <= z);
            init y = y;
            init z = z;
        }
    }

    transition! {
        tr1(n: int) {
            require pre.y <= pre.z;
            require n >= 0;
            update z = pre.z + n;
        }
    }

    readonly! {
        r() {
            require pre.y <= pre.z;
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        self.y <= self.z
    }

    #[inductive(initialize)]
    fn cl_initialize_inductive(post: Self, y: int, z: int) {}

    #[inductive(tr1)]
    fn cl_tr1_inductive(pre: Self, post: Self, n: int) {}
} }

/// Every generated path resolves and has the documented signature. The
/// relations are SPEC functions (ghost at runtime), so they are named here,
/// never called.
#[test]
fn generated_paths_resolve_with_the_documented_signatures() {
    let _init: fn(Cl::State, int, int) -> bool = Cl::State::initialize;
    let _init_enabled: fn(int, int) -> bool = Cl::State::initialize_enabled;
    let _tr1: fn(Cl::State, Cl::State, int) -> bool = Cl::State::tr1;
    let _tr1_strong: fn(Cl::State, Cl::State, int) -> bool = Cl::State::tr1_strong;
    let _tr1_enabled: fn(Cl::State, int) -> bool = Cl::State::tr1_enabled;
    let _r: fn(Cl::State, Cl::State) -> bool = Cl::State::r;
    let _machine_init: fn(Cl::State) -> bool = Cl::State::init;
    let _next: fn(Cl::State, Cl::State) -> bool = Cl::State::next;
    let _next_strong: fn(Cl::State, Cl::State) -> bool = Cl::State::next_strong;
    let _invariant: fn(&Cl::State) -> bool = Cl::State::invariant;
    let _the_inv: fn(&Cl::State) -> bool = Cl::State::the_inv;
    let _lemma: fn(Cl::State, Cl::State, int) = Cl::State::cl_tr1_inductive;
    let _init_lemma: fn(Cl::State, int, int) = Cl::State::cl_initialize_inductive;

    let state = Cl::State { y: 1, z: 2 };
    assert_eq!(state.y, 1);
    assert_eq!(state.z, 2);
}

/// The file lane and the compile lane emit the SAME items, except for the
/// documented compile-only shims.
#[test]
fn the_two_lanes_agree_up_to_the_documented_shims() {
    let input: proc_macro2::TokenStream = r#"
        Parity {
            fields { pub z: int }

            transition! {
                tr(n: int) {
                    update z = pre.z + n;
                }
            }

            #[invariant]
            pub fn inv(&self) -> bool { self.z >= 0 }

            #[inductive(tr)]
            fn parity_tr_inductive(pre: Self, post: Self, n: int) { }
        }
    "#
    .parse()
    .expect("machine body parses");

    let (file_lane, proc_lane) = trust_vc_core::state_machine_dsl::lane_item_labels(input);
    let shims = [
        "mod Parity".to_string(),
        "impl __TvcSm_Parity_State {tr,tr_strong,tr_enabled,init,next,next_strong,parity_tr_inductive}"
            .to_string(),
    ];
    let proc_without_shims: Vec<String> = proc_lane
        .iter()
        .filter(|label| !shims.contains(label))
        .cloned()
        .collect();
    assert_eq!(
        proc_lane.len(),
        proc_without_shims.len() + shims.len(),
        "the compile lane must emit exactly the documented shims: {proc_lane:?}"
    );
    assert_eq!(
        file_lane, proc_without_shims,
        "file-lane and compile-lane item sets should agree once the shims are removed"
    );
}

#[test]
fn a_refused_machine_expands_to_a_compile_error() {
    let input: proc_macro2::TokenStream = "Bad { fields { pub t: nat } }"
        .parse()
        .expect("machine body parses");
    let expanded = trust_vc_core::state_machine_dsl::expand_tokens(input).to_string();
    assert!(
        expanded.contains("compile_error"),
        "a refused machine must emit compile_error!: {expanded}"
    );
    assert!(
        expanded.contains("field `t` has type `nat`"),
        "the compile_error should carry the refusal: {expanded}"
    );
}
