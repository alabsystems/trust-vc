// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

pub(crate) fn verify_with_pipeline(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

pub(crate) fn assume_seq_i64(ctx: &mut VerificationContext, name: &str, values: &[i64]) {
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", values.len()),
    );
    for (index, value) in values.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {value}"),
        );
    }
}

pub(crate) fn assume_seq_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", exprs.len()),
    );
    for (index, expr) in exprs.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {expr}"),
        );
    }
}

pub(crate) fn assume_non_sentinel_i64(ctx: &mut VerificationContext, name: &str) {
    ctx.push_assume(&format!("{name}_non_sentinel"), &format!("{name} != -1"));
}

pub(crate) fn assume_distinct_i64(ctx: &mut VerificationContext, left: &str, right: &str) {
    ctx.push_assume(
        &format!("{left}_{right}_distinct"),
        &format!("{left} != {right}"),
    );
}

pub(crate) fn assume_probe_step(ctx: &mut VerificationContext, next: &str, current: &str, n: &str) {
    ctx.push_assume(
        &format!("{next}_step"),
        &format!(
            "({current} + 1 < {n} && {next} == {current} + 1) || \
             ({current} + 1 >= {n} && {next} == 0)"
        ),
    );
}

pub(crate) fn assume_wrap_probe_indices(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("home", "u64");
    ctx.declare_var_parsed("probe1", "u64");
    ctx.declare_var_parsed("probe2", "u64");
    ctx.declare_var_parsed("probe3", "u64");

    ctx.push_assume("n_val", "n == 4");
    ctx.push_assume("home_val", "home == 2");
    assume_probe_step(ctx, "probe1", "home", "n");
    assume_probe_step(ctx, "probe2", "probe1", "n");
    assume_probe_step(ctx, "probe3", "probe2", "n");
}
