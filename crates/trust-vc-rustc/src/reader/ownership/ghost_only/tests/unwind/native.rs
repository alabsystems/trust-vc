// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native compiler controls; the foreign markers supply no SDK authority.

use super::super::*;

pub(super) fn run(source: &str, inspect: Inspect) {
    run_with_options(source, inspect, ReadOptions::default());
}

pub(super) fn run_with_options(source: &str, inspect: Inspect, options: ReadOptions) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-unwind-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let foreign = directory.0.join("foreign.rs");
    std::fs::write(
        &foreign,
        r#"#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_diagnostic_item = "verus::verus_builtin::no_unwind"]
pub fn no_unwind() {}
#[rustc_diagnostic_item = "verus::verus_builtin::no_unwind_when"]
pub fn no_unwind_when(_condition: bool) {}
#[rustc_diagnostic_item = "verus::verus_builtin::opens_invariants_none"]
pub fn opens_invariants_none() {}
#[rustc_diagnostic_item = "verus::verus_builtin::no_method_body"]
pub fn no_method_body() -> ! { unimplemented!() }
"#,
    )
    .unwrap();
    rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(
            &arguments(&foreign, &directory.0, "unwind_builtin_fixture"),
            &mut Emit,
        )
    })
    .expect("the diagnostic-only builtin fixture must compile");
    let client = directory.0.join("client.rs");
    std::fs::write(
        &client,
        format!(
            r#"#![feature(register_tool, rustc_attrs, stmt_expr_attributes)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, unused_variables, non_snake_case, internal_features)]
{source}
"#
        ),
    )
    .unwrap();
    let mut args = arguments(&client, &directory.0, "unwind_native_client");
    args.extend([
        "--extern".into(),
        format!(
            "unwind_builtin_fixture={}",
            directory
                .0
                .join("libunwind_builtin_fixture.rmeta")
                .display()
        ),
    ]);
    let mut callback = Capture {
        inspect,
        ran: false,
        options,
    };
    let result =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callback));
    assert!(callback.ran, "the actual native callback must run");
    assert!(result.is_ok(), "the component fixture must type check");
}
