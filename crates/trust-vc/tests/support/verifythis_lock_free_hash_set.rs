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
    let len_name = format!("{name}_len");
    let len_cond = format!("{name}.len() == {}", values.len());
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(&len_name, &len_cond);
    for (idx, value) in values.iter().enumerate() {
        let elem_name = format!("{name}_{idx}");
        let elem_cond = format!("{name}.index({idx}) == {value}");
        ctx.push_assume(&elem_name, &elem_cond);
    }
}

pub(crate) fn assume_seq_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    let len_name = format!("{name}_len");
    let len_cond = format!("{name}.len() == {}", exprs.len());
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(&len_name, &len_cond);
    for (idx, expr) in exprs.iter().enumerate() {
        let elem_name = format!("{name}_{idx}");
        let elem_cond = format!("{name}.index({idx}) == {expr}");
        ctx.push_assume(&elem_name, &elem_cond);
    }
}

pub(crate) fn assume_non_sentinel_i64(ctx: &mut VerificationContext, name: &str) {
    let assume_name = format!("{name}_non_sentinel");
    let assume_cond = format!("{name} != -1");
    ctx.push_assume(&assume_name, &assume_cond);
}

pub(crate) fn assume_distinct_i64(ctx: &mut VerificationContext, left: &str, right: &str) {
    let assume_name = format!("{left}_{right}_distinct");
    let assume_cond = format!("{left} != {right}");
    ctx.push_assume(&assume_name, &assume_cond);
}

pub(crate) fn assume_probe_step(ctx: &mut VerificationContext, next: &str, current: &str, n: &str) {
    let cond = format!(
        "({current} + 1 < {n} && {next} == {current} + 1) || ({current} + 1 >= {n} && {next} == 0)"
    );
    let name = format!("{next}_step");
    ctx.push_assume(&name, &cond);
}
