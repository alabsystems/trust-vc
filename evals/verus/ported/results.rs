// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Direct TrustVc port for the active upstream Result success harness cases.
// The negative Result checks live in results_failures.rs so their executable
// counterexample evidence does not inherit the custom datatype axioms here.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CustomErr {
    error_code: i32,
}

#[trust_vc::ensures(true)]
fn test_result() {
    trust_vc::assert!({
        let ok_result = Result::<i8, CustomErr>::Ok(1i8);
        ok_result is Ok
    });
    trust_vc::assert!({
        let ok_result = Result::<i8, CustomErr>::Ok(1i8);
        ok_result.unwrap() == 1i8
    });
    trust_vc::assert!({
        let ok_result = Result::<i8, CustomErr>::Ok(1i8);
        ok_result->Ok_0 == 1i8
    });

    trust_vc::assert!({
        let err_result = Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 });
        err_result is Err
    });
    trust_vc::assert!({
        let err_result = Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 });
        err_result->Err_0 == (CustomErr { error_code: -1i32 })
    });
    trust_vc::assert!({
        let err_result = Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 });
        err_result.unwrap_err() == (CustomErr { error_code: -1i32 })
    });
}

#[trust_vc::ensures(true)]
fn test_result_expect() {
    trust_vc::assert!({
        let ok_result = Result::<i8, CustomErr>::Ok(1i8);
        ok_result is Ok
    });
    trust_vc::assert!({
        let ok_result = Result::<i8, CustomErr>::Ok(1i8);
        ok_result.expect("the result is ok") == 1i8
    });
    trust_vc::assert!({
        let ok_result = Result::<i8, CustomErr>::Ok(1i8);
        ok_result->Ok_0 == 1i8
    });

    trust_vc::assert!({
        let err_result = Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 });
        err_result is Err
    });
    trust_vc::assert!({
        let err_result = Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 });
        err_result->Err_0 == (CustomErr { error_code: -1i32 })
    });
    trust_vc::assert!({
        let err_result = Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 });
        err_result.unwrap_err() == (CustomErr { error_code: -1i32 })
    });
}
