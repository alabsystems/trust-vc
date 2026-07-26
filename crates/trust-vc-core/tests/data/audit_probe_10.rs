// SPDX-License-Identifier: Apache-2.0
// Probe: a named-const pattern (`THREE`) is REFUTABLE and must NOT collapse to an
// irrefutable binding. Value-match form -> exercises IR match_lowering.rs.
const THREE: u64 = 3;

// TARGET -- correct verdict is NOT Verified (Counterexample). In faithful Rust
// `THREE` is a const-pattern matching ONLY x == 3, so for x != 3 the `_` arm
// yields result == x and `ensures(result == 100)` is FALSE. lower_pattern sees a
// bare `syn::Pat::Ident("THREE")`; matches_zero_field_variant(u64, "THREE") is
// false (u64 is not a Datatype), so it lowers to the IRREFUTABLE
// MatchPattern::Ident binding. encode_match_pattern returns None for it, arm 1
// becomes an unconditional match, and result == 100 for every x. A Verified is
// the breach.
#[trust_vc::ensures(result == 100u64)]
fn const_pattern_refinement_must_not_drop(x: u64) -> u64 {
    match x {
        THREE => 100u64,
        _ => x,
    }
}

// POSITIVE control -- a genuine bare binding IS irrefutable; result == x is TRUE
// and must verify (mirrors at_binding_soundness_probe's bare-binding control).
#[trust_vc::ensures(result == x)]
fn plain_binding_is_irrefutable(x: u64) -> u64 {
    match x {
        y => y,
    }
}
