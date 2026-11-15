// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The protocol model built from `#[protocol]`, `#[action]` and `#[safety]`
//! is the Rust the macros annotate, whatever the code around it does.
//!
//! Two cases here used to come back `Verified` with a property that does not
//! hold:
//! - a field's type was read from how it is SPELLED: with `type u64 = u8;` in
//!   scope, a `u8` field spelled `u64` was modelled as a `u64`, and its
//!   overflow at `200 + 100` went unreported;
//! - an action or invariant joined the model only when its function RAN
//!   before collection: an action never called, or an invariant never
//!   evaluated, was left out of the model.
//!
//! Each has a control that is a counterexample. A third case, an action whose
//! `self` is not the protocol, is a compile error
//! (`tests/compile-fail/protocol_component_on_another_type.rs`).
//!
//! Requires the `ty` feature: `targo --unverified test -p trust-vc --features ty`

#![cfg(feature = "ty")]

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

/// In this module `u64` is `u8`: `Counter::x` is a `u8`.
mod aliased {
    #[allow(non_camel_case_types)]
    pub type u64 = u8;

    #[trust_vc::protocol]
    #[derive(Default)]
    pub struct Counter {
        pub x: u64,
    }

    impl Counter {
        #[trust_vc::action(Counter)]
        pub fn step(&mut self) {
            if self.x >= 250 {
                return;
            }
            self.x = self.x + 100;
        }
    }
}

/// The control: the same protocol with the field spelled `u8`.
mod spelled {
    #[trust_vc::protocol]
    #[derive(Default)]
    pub struct Counter {
        pub x: u8,
    }

    impl Counter {
        #[trust_vc::action(Counter)]
        pub fn step(&mut self) {
            if self.x >= 250 {
                return;
            }
            self.x = self.x + 100;
        }
    }
}

/// The twin: an alias of a type wide enough for the same step.
mod wide {
    pub type Word = u16;

    #[trust_vc::protocol]
    #[derive(Default)]
    pub struct Counter {
        pub x: Word,
    }

    impl Counter {
        #[trust_vc::action(Counter)]
        pub fn step(&mut self) {
            if self.x >= 250 {
                return;
            }
            self.x = self.x + 100;
        }
    }
}

/// A field of a type the lane does not model.
mod unmodelled {
    // Only the field types are read.
    #[allow(dead_code)]
    #[trust_vc::protocol]
    #[derive(Default)]
    pub struct Named {
        pub x: u8,
        pub label: String,
    }
}

/// Register a protocol, run `exercise` (which used to decide which of its
/// components were in the model), and verify.
fn verify(register: fn(), exercise: impl FnOnce()) -> VerifyResult {
    common::with_clean_verification(|| {
        register();
        exercise();
        VerificationPipeline::collect_from_macros().verify()
    })
}

/// A counterexample to the property named `property`.
#[track_caller]
fn assert_violates(result: &VerifyResult, property: &str, label: &str) {
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { obligation_name, .. } if obligation_name == property
        ),
        "{label}: expected a counterexample to {property}, got {result:?}"
    );
}

/// `aliased::Counter::x` is a `u8`, so `200 + 100` overflows (a panic in
/// debug). The field was modelled from its spelling `u64` and verified.
#[test]
fn a_field_has_the_type_rust_resolves_not_the_type_it_is_spelled_as() {
    assert_eq!(std::mem::size_of::<aliased::u64>(), 1);
    let control = verify(spelled::Counter::__trust_vc_register_protocol, || {
        spelled::Counter { x: 0 }.step()
    });
    assert_violates(&control, "NoPanic_step", "control, spelled u8");
    let aliased = verify(aliased::Counter::__trust_vc_register_protocol, || {
        aliased::Counter { x: 0 }.step()
    });
    assert_violates(&aliased, "NoPanic_step", "a u8 spelled u64");
    assert_eq!(
        verify(wide::Counter::__trust_vc_register_protocol, || {
            wide::Counter { x: 0 }.step()
        }),
        VerifyResult::Verified,
        "twin: a u16 spelled through an alias holds 300"
    );
    let unmodelled = verify(unmodelled::Named::__trust_vc_register_protocol, || {});
    assert!(
        matches!(&unmodelled, VerifyResult::Error { message } if message.contains("label")),
        "a String field is refused, got {unmodelled:?}"
    );
}

/// `x` counts up to 2 through `up`; `jump` sets it to 7, breaking `small`,
/// and `zero` fails from the first `up`.
mod gate {
    #[trust_vc::protocol]
    #[derive(Default)]
    pub struct Gate {
        pub x: u8,
    }

    impl Gate {
        #[trust_vc::action(Gate)]
        pub fn up(&mut self) {
            if self.x >= 2 {
                return;
            }
            self.x = self.x + 1;
        }

        #[trust_vc::action(Gate)]
        pub fn jump(&mut self) {
            self.x = 7;
        }

        #[trust_vc::safety(Gate)]
        pub fn small(&self) -> bool {
            self.x < 5
        }
    }

    /// The same protocol with a second invariant in place of `jump`.
    #[trust_vc::protocol]
    #[derive(Default)]
    pub struct Still {
        pub x: u8,
    }

    impl Still {
        #[trust_vc::action(Still)]
        pub fn up(&mut self) {
            if self.x >= 2 {
                return;
            }
            self.x = self.x + 1;
        }

        #[trust_vc::safety(Still)]
        pub fn small(&self) -> bool {
            self.x < 5
        }

        #[trust_vc::safety(Still)]
        pub fn zero(&self) -> bool {
            self.x == 0
        }
    }
}

/// Only `up` and `small` run before collection; `jump` is a declared action
/// of `Gate` all the same.
#[test]
fn an_action_that_never_ran_is_in_the_model() {
    use gate::Gate;
    let control = verify(Gate::__trust_vc_register_protocol, || {
        let mut state = Gate { x: 0 };
        state.up();
        state.jump();
        let _ = state.small();
    });
    assert_violates(&control, "small", "control, jump ran");
    let uncalled = verify(Gate::__trust_vc_register_protocol, || {
        let mut state = Gate { x: 0 };
        state.up();
        let _ = state.small();
    });
    assert_violates(&uncalled, "small", "jump never ran");
}

/// Only `up` and `small` run before collection; `zero` is a declared
/// invariant of `Still` all the same.
#[test]
fn an_invariant_never_evaluated_is_in_the_model() {
    use gate::Still;
    let control = verify(Still::__trust_vc_register_protocol, || {
        let mut state = Still { x: 0 };
        state.up();
        let _ = state.small();
        let _ = state.zero();
    });
    assert_violates(&control, "zero", "control, zero evaluated");
    let unevaluated = verify(Still::__trust_vc_register_protocol, || {
        let mut state = Still { x: 0 };
        state.up();
        let _ = state.small();
    });
    assert_violates(&unevaluated, "zero", "zero never evaluated");
}

/// Two protocols of one name in different modules are different protocols:
/// `other::Gate`'s violating action is not part of `twin::Gate`.
mod twin {
    #[trust_vc::protocol]
    #[derive(Default)]
    pub struct Gate {
        pub x: u8,
    }

    impl Gate {
        #[trust_vc::action(Gate)]
        pub fn up(&mut self) {
            if self.x >= 2 {
                return;
            }
            self.x = self.x + 1;
        }

        #[trust_vc::safety(Gate)]
        pub fn small(&self) -> bool {
            self.x < 5
        }
    }

    pub mod other {
        #[trust_vc::protocol]
        #[derive(Default)]
        pub struct Gate {
            pub x: u8,
        }

        impl Gate {
            #[trust_vc::action(Gate)]
            pub fn jump(&mut self) {
                self.x = 7;
            }

            #[trust_vc::safety(Gate)]
            pub fn small(&self) -> bool {
                self.x < 5
            }
        }
    }
}

#[test]
fn a_protocol_is_its_type_not_its_name() {
    let exercise_both = || {
        let mut gate = twin::Gate { x: 0 };
        gate.up();
        let _ = gate.small();
        let mut other = twin::other::Gate { x: 0 };
        other.jump();
        let _ = other.small();
    };
    assert_eq!(
        verify(twin::Gate::__trust_vc_register_protocol, exercise_both),
        VerifyResult::Verified,
        "twin: x stays in 0..2"
    );
    let other = verify(
        twin::other::Gate::__trust_vc_register_protocol,
        exercise_both,
    );
    assert_violates(&other, "small", "the other Gate jumps to 7");
}
