// SpecFn extensionality over Verus-style mathematical int.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::VerifyResult;
use trust_vc_types::{int, nat, SpecFn};

#[test]
fn spec_fn_int_extensional_equality_verifies_without_bit_vector_mode() {
    let result = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn proof_spec_fn_int_successor_extensional(_f: SpecFn<int, int>) {
            trust_vc::assert!(trust_vc::ext_eq!(
                SpecFn::new(|i: int| i + 1),
                SpecFn::new(|j: int| 1 + j)
            ));
        }

        proof_spec_fn_int_successor_extensional(SpecFn::new(|i: int| i));
    });

    assert!(matches!(result, VerifyResult::Verified));
}

#[test]
fn spec_fn_int_extensional_equality_with_nat_offsets_verifies_without_bit_vector_mode() {
    let result = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn proof_spec_fn_int_nat_offsets_extensional(f: SpecFn<int, int>, k1: nat, k2: nat) {
            trust_vc::assert!(trust_vc::ext_eq!(
                SpecFn::new(|n: int| f.call((n + (k2 as int)) + (k1 as int))),
                SpecFn::new(|n: int| f.call(n + ((k1 as int) + (k2 as int))))
            ));
        }

        proof_spec_fn_int_nat_offsets_extensional(SpecFn::new(|i: int| i), 1, 2);
    });

    assert!(matches!(result, VerifyResult::Verified));
}
