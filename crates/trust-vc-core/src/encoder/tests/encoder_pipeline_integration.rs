// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for encoder pipeline paths: datatype encoding,
//! fuel encoding (recursive function termination), and ground pool
//! registration/flush through the full VerificationPipeline.
//!
//! These tests exercise the encoder end-to-end through `AYEncoder::verify()`
//! and `VerificationPipeline`, covering integration points that unit tests
//! for individual modules (datatype.rs, fuel.rs, ground_pool.rs) do not reach.

use super::*;
use crate::ir::TrustVcType;
use crate::vc::{FunctionContext, ProofObligation};
use crate::verification_bridge::VerificationPipeline;

// ---------------------------------------------------------------------------
// Helpers: register datatype function signatures in VerificationContext so
// that prepare_context() can lower string conditions referencing tester,
// constructor, and selector functions.
// ---------------------------------------------------------------------------

/// Registers the Option<u64> tester and constructor function signatures
/// into the VerificationContext's helper function registry so that
/// `prepare_context()` can resolve them during obligation lowering.
fn register_option_u64_datatype_fns(ctx: &mut VerificationContext) {
    let option_ty = TrustVcType::parse_or_opaque("Option<u64>");
    let u64_ty = TrustVcType::Uint { width: 64 };

    // Testers: is_Option_u64_Some(opt) -> bool, is_Option_u64_None(opt) -> bool
    ctx.declare_helper_function_typed(
        "is_Option_u64_Some",
        TrustVcType::Bool,
        vec![("__self".to_string(), option_ty.clone())],
    );
    ctx.declare_helper_function_typed(
        "is_Option_u64_None",
        TrustVcType::Bool,
        vec![("__self".to_string(), option_ty.clone())],
    );

    // Constructor: Option_u64_Some(val) -> Option<u64>
    ctx.declare_helper_function_typed(
        "Option_u64_Some",
        option_ty.clone(),
        vec![("__val".to_string(), u64_ty.clone())],
    );

    // Selector: Option_u64_Some_0(opt) -> u64
    ctx.declare_helper_function_typed(
        "Option_u64_Some_0",
        u64_ty,
        vec![("__self".to_string(), option_ty)],
    );
}

/// Registers the Result<u64, bool> tester function signatures.
fn register_result_u64_bool_datatype_fns(ctx: &mut VerificationContext) {
    let result_ty = TrustVcType::parse_or_opaque("Result<u64, bool>");

    ctx.declare_helper_function_typed(
        "is_Result_u64_bool_Ok",
        TrustVcType::Bool,
        vec![("__self".to_string(), result_ty.clone())],
    );
    ctx.declare_helper_function_typed(
        "is_Result_u64_bool_Err",
        TrustVcType::Bool,
        vec![("__self".to_string(), result_ty)],
    );
}

/// Registers the Option<i32> tester function signatures.
fn register_option_i32_datatype_fns(ctx: &mut VerificationContext) {
    let option_ty = TrustVcType::parse_or_opaque("Option<i32>");

    ctx.declare_helper_function_typed(
        "is_Option_i32_Some",
        TrustVcType::Bool,
        vec![("__self".to_string(), option_ty.clone())],
    );
    ctx.declare_helper_function_typed(
        "is_Option_i32_None",
        TrustVcType::Bool,
        vec![("__self".to_string(), option_ty)],
    );
}

// ---------------------------------------------------------------------------
// 1. Datatype encoding: struct/enum -> ay algebraic datatypes via pipeline
// ---------------------------------------------------------------------------

/// End-to-end: Option<u64> datatype variable declared through
/// VerificationContext, with an assertion about the tester function.
///
/// Exercises: register_builtin_datatypes -> declare_variant_encoding ->
/// assert_datatype_axioms -> tester symbol lookup via verify().
///
/// The assertion `is_Option_u64_Some(opt) || is_Option_u64_None(opt)` is
/// tautological by the exhaustive axiom. If datatype registration or axiom
/// emission is broken, this fails with Unknown or Counterexample.
#[test]
fn test_pipeline_datatype_option_exhaustive_tautology_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u64>"));
    register_option_u64_datatype_fns(&mut ctx);

    // Native datatype exhaustiveness makes this tautological. `is_some()`/
    // `is_none()` lower to the native testers `is-Option_u64_Some`/
    // `is-Option_u64_None` (renamed from the legacy `is_` UF symbols by the
    // native-datatype migration).
    ctx.push_obligation(ProofObligation::assert(
        "exhaustive",
        "opt.is_some() || opt.is_none()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Option<u64> exhaustive tautology should verify through full pipeline",
    );
}

/// End-to-end: Result<u64, bool> with disjointness axiom through pipeline.
///
/// Exercises: multi-variant datatype registration with different field types,
/// tester disjointness axiom. Asserts that is_Ok(res) implies !is_Err(res).
#[test]
fn test_pipeline_datatype_result_disjointness_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res", TrustVcType::parse_or_opaque("Result<u64, bool>"));
    register_result_u64_bool_datatype_fns(&mut ctx);

    // Disjointness: (res is Ok) => !(res is Err). The `is`-variant tests lower to
    // the native testers `is-Result_u64_bool_Ok`/`is-Result_u64_bool_Err`.
    ctx.push_obligation(ProofObligation::assume("is_ok", "res is Ok"));
    ctx.push_obligation(ProofObligation::assert("not_err", "!(res is Err)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result<u64, bool> disjointness should verify: is_Ok => !is_Err",
    );
}

/// End-to-end: Option<u64> constructor + tester roundtrip through
/// VerificationPipeline.
///
/// Exercises: constructor function lookup, tester function lookup,
/// the tester-constructor axiom (is_Some(Some(v)) == true).
///
/// Uses VerificationPipeline (not AYEncoder::verify) to exercise the
/// bridge path.
#[test]
fn test_pipeline_datatype_option_constructor_tester_via_verification_pipeline() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .declare_var_typed("v", TrustVcType::parse_or_opaque("u64"));
    pipeline
        .context_mut()
        .declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u64>"));
    register_option_u64_datatype_fns(pipeline.context_mut());

    // Assume opt == Some(v)
    pipeline.add_obligation(ProofObligation::assume(
        "opt_is_some_v",
        "opt == Option_u64_Some(v)",
    ));

    // Assert the native tester recognizes it as Some. `opt.is_some()` lowers to
    // the native tester `is-Option_u64_Some(opt)` (renamed from the legacy `is_`
    // UF symbol by the native-datatype migration).
    pipeline.add_obligation(ProofObligation::assert("is_some", "opt.is_some()"));

    let result = pipeline.verify();
    expect_verified(
        &result,
        "Option<u64> constructor+tester roundtrip should verify via VerificationPipeline",
    );
}

/// End-to-end: datatype symbols used only inside an obligation expression.
///
/// Regression coverage for obligations that mention Option constructors and
/// testers without any declared `Option<_>` variable in the verification
/// context. Setup must still register the datatype UF symbols before encoding.
#[test]
fn test_pipeline_datatype_expression_only_option_tester_verifies() {
    let mut ctx = VerificationContext::new();

    ctx.push_obligation(ProofObligation::assert(
        "expr_only_option_tester",
        "{ let opt: Option<u32> = if true { Some(42u32) } else { None::<u32> }; opt.is_some() }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Option<u32> used only inside an obligation expression should auto-register",
    );
}

/// End-to-end: Result constructors produced by Option lowering are registered
/// even when neither Option nor Result appears as a declared variable.
#[test]
fn test_pipeline_datatype_expression_only_result_constructor_verifies() {
    let mut ctx = VerificationContext::new();

    ctx.push_obligation(ProofObligation::assert(
        "expr_only_result_constructor",
        "{ let opt: Option<u32> = Some(42u32); opt.ok_or_else(|| 0u32) } == Ok::<u32, u32>(42u32)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result<u32, u32> produced inside an obligation expression should auto-register",
    );
}

// ---------------------------------------------------------------------------
// 2. Fuel encoding: recursive function termination via ay fuel axioms
// ---------------------------------------------------------------------------

/// Environment variable that tells a child copy of this test binary which
/// bounded test body to run.
const BOUNDED_CHILD_ENV: &str = "TRUST_VC_BOUNDED_TEST_CHILD";

/// Resident-memory ceiling for a bounded test's child process.
const BOUNDED_CHILD_MAX_RSS_KIB: u64 = 2 * 1024 * 1024;

/// Wall-clock ceiling for a bounded test's child process.
const BOUNDED_CHILD_MAX_WALL: std::time::Duration = std::time::Duration::from_secs(180);

/// Resident set size of `pid` in KiB, from `ps`; `None` when it cannot be read.
fn child_rss_kib(pid: u32) -> Option<u64> {
    let output = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()?;
    String::from_utf8_lossy(&output.stdout).trim().parse().ok()
}

/// Runs `body` in a child copy of this test binary and fails the test if the
/// child grows past [`BOUNDED_CHILD_MAX_RSS_KIB`] or runs past
/// [`BOUNDED_CHILD_MAX_WALL`].
///
/// A recursive definition whose E-matching expansion outgrows the solver's
/// limits can take all of the machine's memory before any in-process check
/// sees it; one such fuel test once reached 65 GB. The child is killed with
/// SIGKILL at either ceiling, so a regression costs one failed test instead
/// of the machine. The body, and what it asserts, is unchanged; it runs in
/// the child exactly as it would in process.
#[track_caller]
fn run_bounded_in_child(test_name: &str, body: impl FnOnce()) {
    if std::env::var_os(BOUNDED_CHILD_ENV).is_some_and(|name| name == test_name) {
        let query_diagnostic = install_fibonacci_query_diagnostic(test_name);
        body();
        if query_diagnostic {
            eprintln!("TVC_FIB_QUERY_DIAGNOSTIC body-returned");
        }
        return;
    }
    let module = module_path!()
        .split_once("::")
        .map_or(module_path!(), |(_, rest)| rest);
    let exact = format!("{module}::{test_name}");
    let exe = std::env::current_exe().expect("test binary path for the bounded child");
    let mut child = std::process::Command::new(exe)
        .args(["--exact", &exact, "--nocapture", "--test-threads=1"])
        .env(BOUNDED_CHILD_ENV, test_name)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn the bounded child test process");
    let drain = |stream: Option<Box<dyn std::io::Read + Send>>| {
        std::thread::spawn(move || {
            use std::io::Read as _;
            let mut text = String::new();
            if let Some(mut stream) = stream {
                let _ = stream.read_to_string(&mut text);
            }
            text
        })
    };
    let stdout = drain(
        child
            .stdout
            .take()
            .map(|s| Box::new(s) as Box<dyn std::io::Read + Send>),
    );
    let stderr = drain(
        child
            .stderr
            .take()
            .map(|s| Box::new(s) as Box<dyn std::io::Read + Send>),
    );
    let started = std::time::Instant::now();
    let mut peak_kib = 0u64;
    let outcome = loop {
        if let Some(status) = child.try_wait().expect("poll the bounded child") {
            break Ok(status);
        }
        peak_kib = peak_kib.max(child_rss_kib(child.id()).unwrap_or(0));
        let over = if peak_kib > BOUNDED_CHILD_MAX_RSS_KIB {
            Some(format!("resident memory {peak_kib} KiB"))
        } else if started.elapsed() > BOUNDED_CHILD_MAX_WALL {
            Some(format!("wall time {:?}", started.elapsed()))
        } else {
            None
        };
        if let Some(over) = over {
            let _ = child.kill();
            let _ = child.wait();
            break Err(over);
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    };
    let stdout = stdout.join().unwrap_or_default();
    let stderr = stderr.join().unwrap_or_default();
    match outcome {
        Ok(status) if status.success() && stdout.contains("1 passed") => {}
        Ok(status) => {
            panic!("{test_name} failed in its bounded child ({status}):\n{stdout}\n{stderr}")
        }
        Err(over) => panic!(
            "{test_name} was killed at its ceiling: {over} (limits {BOUNDED_CHILD_MAX_RSS_KIB} \
             KiB, {BOUNDED_CHILD_MAX_WALL:?})\n{stdout}\n{stderr}"
        ),
    }
}

/// Diagnostic-copy hook, active only in the existing fresh bounded child.
/// This changes only the query-output directory; the original body and its
/// parent-enforced memory/time ceilings remain the ones above.
fn install_fibonacci_query_diagnostic(test_name: &str) -> bool {
    let Some(directory) = std::env::var_os("TVC_FIB_QUERY_DIAGNOSTIC_DIR") else {
        return false;
    };
    assert_eq!(
        test_name, "test_pipeline_fuel_fibonacci_concrete_wrong_value_not_verified",
        "the diagnostic output is admitted for exactly one original test"
    );
    let directory = std::path::PathBuf::from(directory);
    assert!(
        directory.is_absolute(),
        "Root must bind an absolute output directory"
    );
    let metadata = std::fs::symlink_metadata(&directory).expect("Root-created output directory");
    assert!(metadata.is_dir() && !metadata.file_type().is_symlink());
    assert_eq!(
        std::fs::canonicalize(&directory).expect("physical output directory"),
        directory,
        "Root must bind the canonical physical output path"
    );
    assert!(
        std::fs::read_dir(&directory)
            .expect("read the fresh output directory")
            .next()
            .is_none(),
        "the diagnostic child requires fresh output"
    );
    let directory = directory
        .to_str()
        .expect("the diagnostic directory must be UTF-8")
        .to_owned();
    assert!(
        ay_core::set_global_misc_cli_flags_with(|flags| {
            flags.dump_query_dir = Some(directory);
        }),
        "the output-only flag must be installed before any AY flag capture"
    );
    eprintln!("TVC_FIB_QUERY_DIAGNOSTIC child-entered-before-body");
    true
}

/// A context holding the spec function `name(n: i32) -> i32` and its body
/// axiom `name(n) == body`, triggered on `name(n)`.
fn recursive_i32_fn_ctx(name: &str, body: &str) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: name.to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("i32").unwrap())],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            format!("__body_axiom_{name}"),
            format!("{name}(n) == {body}"),
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec![format!("{name}(n)")]]),
    );
    ctx
}

const FACT_BODY: &str = "{ if n == 0 { 1 } else { n * fact(n - 1) } }";
const FIB_BODY: &str =
    "{ if n == 0 { 0 } else { if n == 1 { 1 } else { fib(n - 1) + fib(n - 2) } } }";

/// End-to-end: factorial base case through full pipeline.
///
/// Exercises: fuel.rs encode_fuel_axioms -> direct defining axiom emission ->
/// E-matching instantiation (1 round for base case).
///
/// fact(0) == 1 is the base case of the recursive definition and requires
/// exactly one E-matching round to unfold.
#[test]
fn test_pipeline_fuel_factorial_base_case_verifies() {
    run_bounded_in_child("test_pipeline_fuel_factorial_base_case_verifies", || {
        let mut ctx = recursive_i32_fn_ctx("fact", FACT_BODY);
        ctx.push_obligation(ProofObligation::assert("fact_0", "fact(0) == 1"));
        expect_verified(
            &AYEncoder::verify(&ctx),
            "fact(0) == 1 should verify (base case, 1 E-matching round)",
        );
    });
}

/// Refuted twin of [`test_pipeline_fuel_factorial_base_case_verifies`].
#[test]
fn test_pipeline_fuel_factorial_base_case_wrong_value_not_verified() {
    run_bounded_in_child(
        "test_pipeline_fuel_factorial_base_case_wrong_value_not_verified",
        || {
            let mut ctx = recursive_i32_fn_ctx("fact", FACT_BODY);
            ctx.push_obligation(ProofObligation::assert("fact_0", "fact(0) == 2"));
            expect_not_verified(&AYEncoder::verify(&ctx), "fact(0) == 2 is false");
        },
    );
}

/// End-to-end: factorial with small concrete input through pipeline.
///
/// Exercises: fuel.rs encode_fuel_axioms -> direct defining axiom ->
/// multi-round E-matching chaining (fact(5) needs 5 unfoldings).
///
/// fact(5) = 5*4*3*2*1 = 120. Five unfoldings are well within ay's
/// E-matching round limit.
#[test]
fn test_pipeline_fuel_factorial_small_concrete_verifies() {
    run_bounded_in_child(
        "test_pipeline_fuel_factorial_small_concrete_verifies",
        || {
            let mut ctx = recursive_i32_fn_ctx("fact", FACT_BODY);
            // fact(5) == 120: needs 5 E-matching rounds
            ctx.push_obligation(ProofObligation::assert("fact_5", "fact(5) == 120"));
            expect_verified(
                &AYEncoder::verify(&ctx),
                "fact(5) == 120 should verify (5 E-matching rounds, within fuel limit)",
            );
        },
    );
}

/// Refuted twin of [`test_pipeline_fuel_factorial_small_concrete_verifies`].
#[test]
fn test_pipeline_fuel_factorial_small_concrete_wrong_value_not_verified() {
    run_bounded_in_child(
        "test_pipeline_fuel_factorial_small_concrete_wrong_value_not_verified",
        || {
            let mut ctx = recursive_i32_fn_ctx("fact", FACT_BODY);
            ctx.push_obligation(ProofObligation::assert("fact_5", "fact(5) == 121"));
            expect_not_verified(&AYEncoder::verify(&ctx), "fact(5) == 121 is false");
        },
    );
}

/// End-to-end: Fibonacci through pipeline with multi-recursive body axiom.
///
/// Exercises: fuel encoding with a function body that contains TWO recursive
/// calls (fib(n-1) + fib(n-2)), testing that E-matching chains correctly
/// through both branches of the recursion tree.
///
/// fib(0)=0, fib(1)=1, fib(5)=5 needs: fib(5)=fib(4)+fib(3),
/// fib(4)=fib(3)+fib(2), etc. The tree flattens to ~5 distinct calls. The
/// symbolic `fib(n)` terms in the context also seed the axiom, and each of
/// their unfoldings mints two more calls; this is the test that once ran the
/// solver out of memory, hence the bounded child.
#[test]
fn test_pipeline_fuel_fibonacci_concrete_verifies() {
    run_bounded_in_child("test_pipeline_fuel_fibonacci_concrete_verifies", || {
        let mut ctx = recursive_i32_fn_ctx("fib", FIB_BODY);
        // fib(5) == 5: exercises multi-recursive unfolding
        ctx.push_obligation(ProofObligation::assert("fib_5", "fib(5) == 5"));
        expect_verified(
            &AYEncoder::verify(&ctx),
            "fib(5) == 5 should verify with multi-recursive E-matching chaining",
        );
    });
}

/// Refuted twin of [`test_pipeline_fuel_fibonacci_concrete_verifies`].
#[test]
fn test_pipeline_fuel_fibonacci_concrete_wrong_value_not_verified() {
    run_bounded_in_child(
        "test_pipeline_fuel_fibonacci_concrete_wrong_value_not_verified",
        || {
            let mut ctx = recursive_i32_fn_ctx("fib", FIB_BODY);
            ctx.push_obligation(ProofObligation::assert("fib_5", "fib(5) == 6"));
            expect_not_verified(&AYEncoder::verify(&ctx), "fib(5) == 6 is false");
        },
    );
}

// ---------------------------------------------------------------------------
// 3. Ground pool: registration and flush through the verify pipeline
// ---------------------------------------------------------------------------

/// End-to-end: ground pool flush integrates with broadcast axiom instantiation
/// through the full verification pipeline.
///
/// Exercises: ground_pool.register -> register_axiom -> flush_ground_axioms_to_fixpoint
/// through AYEncoder::verify(). The broadcast axiom `forall j: a.index(j) >= 0`
/// is instantiated via ground pool seeding when `a.index(0)` appears in the goal.
///
/// Without ground pool flush, the quantified broadcast has no ground trigger
/// terms and the solver returns Unknown.
#[test]
fn test_pipeline_ground_pool_broadcast_instantiation_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("j", TrustVcType::parse_or_opaque("u64"));

    ctx.push_obligation(ProofObligation::assume("len_bound", "a.len() > 0"));

    // Broadcast: all elements are non-negative
    ctx.obligations.push(
        ProofObligation::broadcast_assume("all_nonneg", "a.index(j) >= 0")
            .with_bound_vars(vec!["j".to_string()])
            .with_trigger_patterns(vec![vec!["a.index(j)".to_string()]]),
    );

    // Assert element 0 is non-negative (ground pool + E-matching)
    ctx.push_obligation(ProofObligation::assert("elem_0_nonneg", "a.index(0) >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ground pool flush should instantiate broadcast for a.index(0) >= 0",
    );
}

/// End-to-end: ground pool with spec function body axiom and ground term reuse.
///
/// Exercises the interaction between fuel encoding (which registers body
/// axioms with the ground pool) and flush_ground_axioms_to_fixpoint (which
/// instantiates them for concrete call sites).
///
/// The spec function `double(n) == n + n` is defined as a body axiom.
/// The ground pool should register the axiom, and when `double(5)` appears
/// in the assertion, flush should instantiate `double(5) == 5 + 5 == 10`.
#[test]
fn test_pipeline_ground_pool_fuel_body_axiom_flush_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![("n".to_string(), TrustVcType::from_str("i32").unwrap())],
        return_type: TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axiom: double(n) == n + n
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(n) == n + n")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["double(n)".to_string()]]),
    );

    // Assert double(5) == 10
    ctx.push_obligation(ProofObligation::assert("double_5", "double(5) == 10"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ground pool should flush body axiom for double(5) == 10",
    );
}

/// End-to-end: VerificationPipeline with both datatype and fuel encoding
/// exercised simultaneously.
///
/// Exercises the interaction between datatype registration (Option<i32>)
/// and spec function body axiom (abs(n)), verifying that both encoder
/// subsystems coexist correctly in a single pipeline run.
#[test]
fn test_pipeline_combined_datatype_and_fuel_coexist() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .declare_var_typed("n", TrustVcType::parse_or_opaque("i32"));
    pipeline
        .context_mut()
        .declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<i32>"));
    register_option_i32_datatype_fns(pipeline.context_mut());

    pipeline
        .context_mut()
        .set_function_context(FunctionContext {
            name: "abs".to_string(),
            params: vec![("n".to_string(), TrustVcType::from_str("i32").unwrap())],
            return_type: TrustVcType::from_str("i32").unwrap(),
            is_recursive: false,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: vec![],
        });

    // Body axiom: abs(n) == if n >= 0 { n } else { 0 - n }
    pipeline.context_mut().obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_abs",
            "abs(n) == { if n >= 0 { n } else { 0 - n } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["abs(n)".to_string()]]),
    );

    // abs(5) == 5 exercises the fuel/body axiom path
    pipeline.add_obligation(ProofObligation::assert("abs_positive", "abs(5) == 5"));

    // Option exhaustive tautology exercises the datatype path. `is_some()`/
    // `is_none()` lower to the native testers `is-Option_i32_Some`/
    // `is-Option_i32_None`.
    pipeline.add_obligation(ProofObligation::assert(
        "opt_exhaustive",
        "opt.is_some() || opt.is_none()",
    ));

    let result = pipeline.verify();
    expect_verified(
        &result,
        "combined datatype + fuel should verify through VerificationPipeline",
    );
}
