//! Traits: method declarations without bodies, implementations that inherit
//! the declaration's clauses, default methods, calls resolved to an
//! implementation, to an instance or to the declaration, and the rules
//! Verus checks on them. Each program has a twin that differs from it in
//! one line.
//!
//! The programs are in `traits/<name>.rs` and their twins in
//! `traits/<name>.twin.rs`, from the `verus!` line on (line 1). Every
//! expected verdict, message and line is that of the reference Verus+z3 run
//! on the same program, except where the expected outcome is a refusal. The
//! binary needs the trustc-built `verus_builtin` crates (see `common`).

mod common;

/// A run's outcome and its errors, as message prefixes and the line of their
/// first primary span.
type Expect = (&'static str, &'static [(&'static str, usize)]);

const CHECKED: Expect = ("checked", &[]);

const fn failed(errors: &'static [(&'static str, usize)]) -> Expect {
    ("verification-failed", errors)
}

const fn rejected(errors: &'static [(&'static str, usize)]) -> Expect {
    ("verus-rejected", errors)
}

const ASSERT: &str = "assertion failed";
const POST: &str = "postcondition not satisfied";
const PRE: &str = "precondition not satisfied";
const RECURSION: &str = "recursive function must have a decreases clause";
const CYCLE: &str =
    "found a cyclic self-reference in a definition, which may result in nontermination";

struct Case {
    name: &'static str,
    program: &'static str,
    twin: &'static str,
    expect: Expect,
    twin_expect: Expect,
}

macro_rules! case {
    ($name:literal, $expect:expr, $twin_expect:expr) => {
        Case {
            name: $name,
            program: include_str!(concat!("traits/", $name, ".rs")),
            twin: include_str!(concat!("traits/", $name, ".twin.rs")),
            expect: $expect,
            twin_expect: $twin_expect,
        }
    };
}

const CASES: &[Case] = &[
    // A declaration without a body has nothing to check; `open` on one is
    // Verus's error.
    case!(
        "bodyless_decl",
        CHECKED,
        rejected(&[(
            "trait function declarations cannot be open or closed, as they don't have a body",
            3
        )])
    ),
    // An implementation must meet the declaration's `ensures`, reported at
    // the declaration's clause.
    case!("impl_inherits_ensures", CHECKED, failed(&[(POST, 4)])),
    // A call is checked against the declaration's `requires`.
    case!("call_checks_decl_requires", CHECKED, failed(&[(PRE, 11)])),
    // A call resolved to an implementation assumes that implementation's
    // own `ensures`; through a type parameter only the declaration's.
    case!("static_call_impl_ensures", CHECKED, failed(&[(ASSERT, 16)])),
    // Calls at two type parameters are different applications.
    case!("dispatch_type_args", CHECKED, failed(&[(ASSERT, 6)])),
    // An implementation that does not override a default spec method gets
    // its body.
    case!("default_instance", CHECKED, failed(&[(ASSERT, 8)])),
    // Through a type parameter a default body is not known: an
    // implementation may override it.
    case!("default_not_generic", CHECKED, failed(&[(ASSERT, 6)])),
    // An override replaces the default body.
    case!("override_default", CHECKED, failed(&[(ASSERT, 10)])),
    // A default exec method is checked once, for every `Self`, from the
    // declarations it calls.
    case!("exec_default_body", CHECKED, failed(&[(POST, 6)])),
    // An implementation cannot declare `requires`.
    case!(
        "impl_requires",
        CHECKED,
        rejected(&[(
            "trait method implementation cannot declare requires clauses",
            7
        )])
    ),
    // An implementation has the declaration's mode.
    case!(
        "impl_mode",
        CHECKED,
        rejected(&[("function must have mode spec", 7)])
    ),
    // `no_method_body()` belongs in a declaration's specification method.
    case!(
        "no_method_body_default",
        CHECKED,
        rejected(&[(
            "no_method_body can only appear in trait method declarations",
            3
        )])
    ),
    // A spec method implemented in a public trait needs `open` or `closed`.
    case!(
        "open_closed_required",
        CHECKED,
        rejected(&[(
            "open/closed is required for implementations of non-private traits",
            8
        )])
    ),
    // A cycle through a trait bound and the implementation: Verus's error,
    // at the first function of the cycle.
    case!("trait_cycle", CHECKED, rejected(&[(CYCLE, 7)])),
    // A blanket implementation whose method needs the implementation
    // itself.
    case!("cycle_blanket_impl", CHECKED, rejected(&[(CYCLE, 4)])),
    // A default method that calls a function bounded by its own trait.
    case!("cycle_default_method", CHECKED, rejected(&[(CYCLE, 2)])),
    // Exec functions: the implementation's method calls a function that
    // needs the implementation.
    case!("cycle_exec", CHECKED, rejected(&[(CYCLE, 5)])),
    // Two implementations that need each other through a generic
    // implementation's bound.
    case!("cycle_generic_impls", CHECKED, rejected(&[(CYCLE, 5)])),
    // A generic implementation of a subtrait needs the supertrait's
    // implementation, which uses it.
    case!("cycle_supertrait", CHECKED, rejected(&[(CYCLE, 8)])),
    // A cycle of calls through Verus's copy of an inherited default method:
    // Verus's error for recursion without `decreases`.
    case!(
        "recursion_through_default",
        CHECKED,
        rejected(&[(RECURSION, 6)])
    ),
    // A generic spec function called at a concrete type has the body it
    // has at that type.
    case!("generic_spec_instance", CHECKED, failed(&[(ASSERT, 11)])),
    // An implementation for a primitive type.
    case!("impl_for_u8", CHECKED, failed(&[(ASSERT, 13)])),
    // Implementations of one trait at two type arguments.
    case!("trait_type_args", CHECKED, failed(&[(ASSERT, 7)])),
    // A field read through `&self`.
    case!("field_through_self", CHECKED, failed(&[(ASSERT, 10)])),
    // A call with an explicit shared borrow.
    case!("explicit_borrow_call", CHECKED, failed(&[(ASSERT, 12)])),
    // A `Drop` implementation is checked like any function.
    case!(
        "drop_impl",
        CHECKED,
        failed(&[("possible arithmetic underflow/overflow", 9)])
    ),
    // A cycle of calls without `decreases` is Verus's error: through a
    // spec body, through proof calls, and through a method calling itself
    // on its implementation.
    case!("recursion_spec", CHECKED, rejected(&[(RECURSION, 2)])),
    case!(
        "recursion_proof_mutual",
        CHECKED,
        rejected(&[(RECURSION, 2)])
    ),
    case!(
        "recursion_through_impl",
        CHECKED,
        rejected(&[(RECURSION, 7)])
    ),
    // A `Drop` implementation must be marked `no_unwind`.
    case!(
        "drop_no_unwind",
        CHECKED,
        rejected(&[("the implementation for Drop must be marked no_unwind", 4)])
    ),
];

/// The number of lines in which two programs differ.
fn differing_lines(a: &str, b: &str) -> usize {
    let (a, b): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if a.len() != b.len() {
        return usize::MAX;
    }
    a.iter().zip(&b).filter(|(x, y)| x != y).count()
}

fn check(name: &str, program: &str, (outcome, want): Expect) -> Vec<String> {
    let run = common::run(name, program, &[]);
    let mut problems = Vec::new();
    if run.outcome() != outcome {
        problems.push(format!(
            "{name}: outcome {} instead of {outcome}",
            run.outcome()
        ));
    }
    let errors: Vec<(String, usize)> = run
        .errors()
        .iter()
        .map(|d| {
            (
                d.message.clone(),
                d.primary_lines.first().copied().unwrap_or(0),
            )
        })
        .collect();
    let matches = errors.len() == want.len()
        && errors
            .iter()
            .zip(want)
            .all(|((message, line), (prefix, want_line))| {
                message.starts_with(prefix) && line == want_line
            });
    if !matches {
        problems.push(format!("{name}: errors {errors:?} instead of {want:?}"));
    }
    if !run.raw.is_empty() {
        problems.push(format!("{name}: non-JSON stderr {:?}", run.raw));
    }
    if outcome == "checked" && run.exit != 0 {
        problems.push(format!("{name}: exit {} for a checked run", run.exit));
    }
    problems
}

#[test]
fn traits_and_their_twins() {
    let mut problems = Vec::new();
    for case in CASES {
        assert_eq!(
            differing_lines(case.program, case.twin),
            1,
            "{}: the twin is not a one-line change",
            case.name
        );
        problems.extend(check(case.name, case.program, case.expect));
        let twin = format!("{}__twin", case.name);
        problems.extend(check(&twin, case.twin, case.twin_expect));
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// A substituted associated type must select its real implementation and keep
/// its dependency edges. The twin closes a cycle through the same native
/// projection; neither an ICE nor dropping that dependency is an accepted result.
#[test]
fn substituted_projection_bounds_keep_their_cycle_dependencies() {
    let positive = include_str!("traits/normalized_projection_bound.rs");
    let negative = include_str!("traits/normalized_projection_bound.twin.rs");
    assert_eq!(differing_lines(positive, negative), 1);
    let good = common::run("normalized_projection_bound", positive, &[]);
    assert_eq!(good.outcome(), "checked");
    assert_eq!(good.exit, 0);
    assert!(good.errors().is_empty());
    assert!(good.raw.is_empty());
    let bad = common::run("normalized_projection_bound__cycle", negative, &[]);
    assert_eq!(bad.outcome(), "verus-rejected");
    assert_ne!(bad.exit, 0);
    let messages: Vec<String> = bad
        .errors()
        .iter()
        .map(|error| error.message.clone())
        .collect();
    assert_eq!(messages, vec![CYCLE.to_owned()]);
    assert!(bad.raw.is_empty());
}
