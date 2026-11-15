// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-9 RESIDUAL CONTROL. Byte-identical to
// `const_scope_contamination_repro.rs` except for the NAME of a `const` item
// declared inside a DIFFERENT function's body. `zc_shadow_cx` is unchanged, so
// any verdict difference between the two files is bought by that name alone.

#[trust_vc::ensures(true)]
fn zc_shadow_cx(v: Seq<u64>, w: Vec<u64>) {
    match w {
        v => {
            let _ = v.map(|_x| 10u64 / 0u64);
        }
    }
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zc_unrelated_function_with_a_body_const_other_name(z: u64) {
    const qqq: [u64; 3] = [1u64, 2u64, 3u64];
    trust_vc::assert!(true);
}
