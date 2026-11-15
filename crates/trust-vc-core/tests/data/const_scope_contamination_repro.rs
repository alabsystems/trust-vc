// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-9 RESIDUAL FIXTURE. `zc_shadow_cx` is a match-arm shadow of a spec
// parameter over an exec value; its closure body ALWAYS divides by zero, so a
// `Verified` is a FALSE VERIFY. Nothing in THIS function changes between this
// file and its control twin — only the NAME of a `const` item declared inside
// a DIFFERENT function's body.

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
fn zc_unrelated_function_with_a_body_const(z: u64) {
    const v: [u64; 3] = [1u64, 2u64, 3u64];
    trust_vc::assert!(true);
}
