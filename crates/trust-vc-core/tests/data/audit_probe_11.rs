// SPDX-License-Identifier: Apache-2.0
// Probe: a struct-field LITERAL refinement (`Cell { v: 0, .. }`) must NOT be
// dropped. Distinct pattern NODE (Pat::Struct) from the tuple-struct probe.
struct Cell {
    v: u64,
    w: u64,
}

// TARGET -- correct verdict is NOT Verified (Counterexample). Faithfully, arm 1
// `Cell { v: 0, .. }` matches ONLY c.v == 0; arm 2 `Cell { v, .. }` is reached for
// every c with c.v != 0, where `assert!(v == 0)` is FALSE. The obligation
// collector's pattern_match_condition_for_scoped_value returns the irrefutable
// "true" for a single-variant struct and never inspects struct_pat.fields, so the
// `v: 0` refinement is discarded: arm 1 becomes an unconditional match,
// prior_negations becomes `!(true)`, arm 2's path condition is `!(true)` == false,
// and add_assertion guards `v == 0` as `!(!(true)) || (v==0)` == true. A Verified
// is the breach.
#[trust_vc::ensures(true)]
fn struct_field_literal_refinement_must_not_drop(c: Cell) {
    match c {
        Cell { v: 0, .. } => {}
        Cell { v, .. } => {
            trust_vc::assert!(v == 0u64);
        }
    }
}

// POSITIVE control -- a true arm-assert over a projected struct field must verify.
#[trust_vc::ensures(true)]
fn struct_field_true_assert_verifies(c: Cell) {
    match c {
        Cell { v, .. } => {
            trust_vc::assert!(v == v);
        }
    }
}
