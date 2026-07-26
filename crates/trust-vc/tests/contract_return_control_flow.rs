// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Runtime coverage for `#[trust_vc::contract(..., returns(...))]` early-return
//! capture from nested control-flow constructs.

#![allow(
    clippy::let_and_return,
    clippy::needless_return,
    clippy::never_loop,
    clippy::overly_complex_bool_expr,
    clippy::while_immutable_condition
)]

mod common;

use trust_vc_core::VerifyResult;

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_match_arm_contract(flag: bool) -> u64 {
    match flag {
        true => {
            return 11u64;
        }
        false => 13u64,
    }
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_loop_contract(flag: bool) -> u64 {
    loop {
        if flag {
            return 11u64;
        }
        break;
    }
    13u64
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_local_initializer_contract(flag: bool) -> u64 {
    let value: u64 = if flag {
        return 11u64;
    } else {
        17u64
    };
    value
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_if_let_expression_contract(maybe: Option<u64>) -> u64 {
    let value = if let Some(value) = maybe {
        value
    } else {
        return 13u64;
    };
    value
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 13u64),
    returns(result),
)]
fn return_from_let_else_contract(maybe: Option<u64>) -> u64 {
    let Some(value) = maybe else {
        return 13u64;
    };
    value
}

fn identity_u64(value: u64) -> u64 {
    value
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_call_argument_contract(flag: bool) -> u64 {
    identity_u64(if flag {
        return 11u64;
    } else {
        17u64
    })
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_from_short_circuit_expression_contract(flag: bool) -> u64 {
    if flag || {
        return 11u64;
    } {
        17u64
    } else {
        13u64
    }
}

#[trust_vc::contract(
    ensures(result == 11u64 || result == 17u64),
    returns(result),
)]
fn return_with_nested_impl_method_contract(flag: bool) -> u64 {
    struct Local;
    impl Local {
        fn value() -> u64 {
            return 11u64;
        }
    }

    if flag {
        return Local::value();
    }
    17u64
}

#[trust_vc::contract(
    requires(flag),
    ensures(result == ()),
    returns(result),
)]
fn return_from_while_with_invariant_contract(flag: bool) {
    while flag || !flag {
        trust_vc::invariant!(flag);
        return;
    }
}

#[trust_vc::contract(ensures(false), returns(result))]
fn false_postcondition_from_local_initializer_return(flag: bool) -> u64 {
    let value: u64 = if flag {
        return 11u64;
    } else {
        17u64
    };
    value
}

#[trust_vc::contract(ensures(false), returns(result))]
fn false_postcondition_from_call_argument_return(flag: bool) -> u64 {
    identity_u64(if flag {
        return 11u64;
    } else {
        17u64
    })
}

#[trust_vc::contract(ensures(result == 17u64), returns(result))]
fn false_postcondition_from_short_circuit_return(flag: bool) -> u64 {
    if flag || {
        return 11u64;
    } {
        17u64
    } else {
        13u64
    }
}

#[test]
fn contract_return_from_match_arm_captures_both_paths() {
    common::with_clean_verification(|| {
        assert_eq!(return_from_match_arm_contract(true), 11u64);
    });
    common::with_clean_verification(|| {
        assert_eq!(return_from_match_arm_contract(false), 13u64);
    });
}

#[test]
fn contract_return_from_loop_captures_return_and_fallthrough_paths() {
    common::with_clean_verification(|| {
        assert_eq!(return_from_loop_contract(true), 11u64);
    });
    common::with_clean_verification(|| {
        assert_eq!(return_from_loop_contract(false), 13u64);
    });
}

#[test]
fn contract_return_from_local_initializer_captures_both_paths() {
    common::with_clean_verification(|| {
        assert_eq!(return_from_local_initializer_contract(true), 11u64);
    });
    common::with_clean_verification(|| {
        assert_eq!(return_from_local_initializer_contract(false), 17u64);
    });
}

#[test]
fn contract_return_from_if_let_expression_captures_both_paths() {
    common::with_clean_verification(|| {
        assert_eq!(return_from_if_let_expression_contract(Some(11u64)), 11u64);
    });
    common::with_clean_verification(|| {
        assert_eq!(return_from_if_let_expression_contract(None), 13u64);
    });
}

#[test]
fn contract_return_from_let_else_captures_both_paths() {
    common::with_clean_verification(|| {
        assert_eq!(return_from_let_else_contract(Some(11u64)), 11u64);
    });
    common::with_clean_verification(|| {
        assert_eq!(return_from_let_else_contract(None), 13u64);
    });
}

#[test]
fn contract_return_from_call_argument_captures_both_paths() {
    common::with_clean_verification(|| {
        assert_eq!(return_from_call_argument_contract(true), 11u64);
    });
    common::with_clean_verification(|| {
        assert_eq!(return_from_call_argument_contract(false), 17u64);
    });
}

#[test]
fn contract_return_from_short_circuit_expression_captures_both_paths() {
    common::with_clean_verification(|| {
        assert_eq!(return_from_short_circuit_expression_contract(true), 17u64);
    });
    common::with_clean_verification(|| {
        assert_eq!(return_from_short_circuit_expression_contract(false), 11u64);
    });
}

#[test]
fn contract_return_skips_nested_impl_method_return_scope() {
    common::with_clean_verification(|| {
        assert_eq!(return_with_nested_impl_method_contract(true), 11u64);
    });
    common::with_clean_verification(|| {
        assert_eq!(return_with_nested_impl_method_contract(false), 17u64);
    });
}

#[test]
fn contract_return_from_while_with_invariant_captures_unit_return() {
    common::with_clean_verification(|| {
        return_from_while_with_invariant_contract(true);
    });
}

#[test]
fn contract_return_from_local_initializer_still_checks_false_postcondition() {
    let result = common::verify_and_get_result(|| {
        assert_eq!(
            false_postcondition_from_local_initializer_return(true),
            11u64
        );
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition on a captured local-initializer return should fail, got: {result:?}"
    );
}

#[test]
fn contract_return_from_call_argument_still_checks_false_postcondition() {
    let result = common::verify_and_get_result(|| {
        assert_eq!(false_postcondition_from_call_argument_return(true), 11u64);
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition on a captured call-argument return should fail, got: {result:?}"
    );
}

#[test]
fn contract_return_from_short_circuit_still_checks_false_postcondition() {
    let result = common::verify_and_get_result(|| {
        assert_eq!(false_postcondition_from_short_circuit_return(false), 11u64);
    });

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "false postcondition on a captured short-circuit return should fail, got: {result:?}"
    );
}
