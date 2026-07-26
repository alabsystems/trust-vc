// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Soundness probe: a recursive specification function with NO #[decreases] must
// not let the engine prove a false statement. Verus admits a recursive
// definition's axiom only after discharging a `decreases` termination proof;
// without that proof the axiom `forall n. bad(n) == bad(n) + 1` has no model and
// entails anything.

#[trust_vc::spec]
fn bad(n: u64) -> u64 {
    bad(n) + 1
}

// FALSE for every value of bad(3) (bad(3)+100 == bad(3) iff 100 == 0). Only
// derivable from the contradictory recursive defining axiom. The call bad(3)
// fires the {bad(n)} trigger so the axiom instantiates.
#[trust_vc::ensures(true)]
fn repro_proves_false() {
    trust_vc::assert!(bad(3u64) == bad(3u64) + 100u64);
}

// Control: a plainly false statement that does NOT mention bad() must not
// verify (guards against the test passing for an unrelated reason).
#[trust_vc::ensures(true)]
fn control_false_without_axiom() {
    trust_vc::assert!(1u64 == 2u64);
}
