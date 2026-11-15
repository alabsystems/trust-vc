//! Quantifiers, triggers and choices: `forall` and `exists` as facts and
//! as goals, instances only where a trigger matches a relevant term,
//! `choose`, `assert forall .. by`, and the trigger errors Verus reports.
//! Each program has a twin that differs from it in one line.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The programs are in `quantifiers/<name>.rs` and their twins in
//! `quantifiers/<name>.twin.rs`, from the `verus!` line on (line 1). Every
//! expected verdict, message and line is that of the reference Verus+z3
//! run on the same program. The binary needs the trustc-built
//! `verus_builtin` crates (see `common`).

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
            program: include_str!(concat!("quantifiers/", $name, ".rs")),
            twin: include_str!(concat!("quantifiers/", $name, ".twin.rs")),
            expect: $expect,
            twin_expect: $twin_expect,
        }
    };
}

const CASES: &[Case] = &[
    // A `forall` fact is instantiated at the goal's term; an `exists` fact
    // is not.
    case!("forall_requires", CHECKED, failed(&[(ASSERT, 7)])),
    // Only a term that matches a trigger is an instance: the twin's
    // trigger `p(i)` matches nothing, although `q(3)` follows in
    // first-order logic.
    case!("trigger_gates", CHECKED, failed(&[(ASSERT, 8)])),
    // The hypothesis `p(3)` matches the rule's trigger; `p(4)` gives the
    // instance at 4.
    case!("implication_rule", CHECKED, failed(&[(ASSERT, 10)])),
    // An `exists` goal is proved at the witness the hypothesis supplies.
    case!("exists_goal", CHECKED, failed(&[(ASSERT, 7)])),
    // An automatic trigger: `tr(300)` is the witness; without it there is
    // none (quantifiers.rs `test1`, `test1_fails`).
    case!("exists_auto_witness", CHECKED, failed(&[(ASSERT, 8)])),
    // A `forall` goal: its counterexample's `p` term instantiates the
    // hypothesis.
    case!("forall_goal", CHECKED, failed(&[(ASSERT, 8)])),
    // A bound variable has its type's range.
    case!("bounded_var", CHECKED, failed(&[(ASSERT, 5)])),
    // A trigger of two terms matches only where both are relevant: the
    // twin's `p(3) && q(4)` makes one of them relevant at a time.
    case!("multi_trigger_relevant", CHECKED, failed(&[(ASSERT, 8)])),
    // `choose` satisfies its condition when some value does; the twin
    // knows only that some value satisfies `q`.
    case!("choose_satisfies", CHECKED, failed(&[(ASSERT, 9)])),
    // Choices equal up to their holes choose the same value; the twin's
    // condition has another shape (choose.rs `test1`, `test1_fails3`).
    case!("choose_holes", CHECKED, failed(&[(ASSERT, 7)])),
    // `assert forall .. implies .. by` is assumed after its proof.
    case!("assert_forall_by", CHECKED, failed(&[(ASSERT, 18)])),
    // Verus's errors.
    case!(
        "trigger_cover",
        CHECKED,
        rejected(&[("trigger does not cover variable j", 6)])
    ),
    case!(
        "no_trigger",
        CHECKED,
        rejected(&[(
            "Could not automatically infer triggers for this quantifier.",
            5
        )])
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
fn quantifiers_and_their_twins() {
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

/// Real native HIR array carriers must expose their members before the
/// assert-forall clause-count check. No conjunction or saved proof replaces
/// the at most one requires and exactly one ensures the upstream reader permits.
#[test]
fn assert_forall_array_headers_preserve_single_clauses_and_false_twins() {
    for (index, header) in [
        "requires([true]); ensures([true]);",
        "verus_builtin::requires::<[bool; 0]>([]); ensures([true]);",
        "requires([true]); ensures([verus_builtin::constrain_type(0u8, 0u8), true]);",
        "requires([true]); ensures([true, verus_builtin::constrain_type(0u8, 0u8)]);",
        "requires([true]); ensures([verus_builtin::constrain_type(0u8, 0u8), true, verus_builtin::constrain_type(0u8, 0u8)]);",
    ].into_iter().enumerate() {
        let source = format!("verus! {{ proof fn test() {{ verus_builtin::assert_forall_by(|| {{ {header} }}); }} }}");
        let result = common::run(&format!("forall_array_single_{index}"), &source, &[]);
        assert_eq!(result.exit, 0, "{result:?}");
        assert_eq!(result.outcome(), "checked", "{result:?}");
        assert_eq!(result.record["erase_exit"], 0, "{result:?}");
        assert!(result.errors().is_empty() && result.raw.is_empty(), "{result:?}");
        assert!(result.record["crate_refusals"].as_array().unwrap().is_empty(), "{result:?}");
    }
    let binder = "verus! { spec fn tag(i: int) -> bool { i == i } proof fn test() { verus_builtin::assert_forall_by(|i: int| { requires([tag(i)]); ensures([#[trigger] tag(i)]); }); } }";
    let result = common::run("forall_array_actual_binder", binder, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
    assert!(
        result.errors().is_empty() && result.raw.is_empty(),
        "{result:?}"
    );
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );

    // The same intrinsic filtering rule applies to ordinary function and BV
    // ensures; a mode-only fix must not leave their readers counting the aid.
    for (index, source) in [
        "verus! { proof fn test() { ensures([true, verus_builtin::constrain_type(0u8, 0u8)]); } }",
        "verus! { proof fn test() { verus_builtin::assert_bitvector_by({ ensures([true, verus_builtin::constrain_type(0u8, 0u8)]); }); } }",
        "verus! { fn effect() -> bool { true } fn test() { loop { ensures([true, verus_builtin::constrain_type(effect(), true)]); verus_builtin::decreases(0u8); break; } } }",
        "verus! { fn test() { loop { ensures(true); verus_builtin::decreases(0u8); break; } } }",
    ].into_iter().enumerate() {
        let result = common::run(&format!("ensures_array_context_{index}"), source, &[]);
        assert_eq!(result.exit, 0, "{result:?}");
        assert_eq!(result.outcome(), "checked", "{result:?}");
        assert_eq!(result.record["erase_exit"], 0, "{result:?}");
        assert!(result.errors().is_empty() && result.raw.is_empty(), "{result:?}");
        assert!(result.record["crate_refusals"].as_array().unwrap().is_empty(), "{result:?}");
    }

    let source = "verus! { proof fn test() { verus_builtin::assert_forall_by(|| { requires([true]); ensures([false]); }); } }";
    let result = common::run("forall_array_false_twin", source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .unwrap();
    assert_eq!(proof["verdict"], "failed", "{result:?}");
    assert_eq!(proof["sites_failed"], 1, "{result:?}");
    assert_eq!(
        result
            .errors()
            .iter()
            .map(|error| error.message.as_str())
            .collect::<Vec<_>>(),
        [ASSERT],
        "{result:?}"
    );

    // The loop retains its actual Bool clause after erasing the typing aid.
    let source = "verus! { fn effect() -> bool { true } fn test() { loop { ensures([false, verus_builtin::constrain_type(effect(), true)]); verus_builtin::decreases(0u8); break; } } }";
    let result = common::run("loop_ensures_array_false_twin", source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.record["erase_exit"], 0, "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );
    let proof = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "test")
        .unwrap();
    assert_eq!(proof["verdict"], "failed", "{result:?}");
    assert_eq!(proof["sites_failed"], 1, "{result:?}");
    assert_eq!(
        result
            .errors()
            .iter()
            .map(|error| error.message.as_str())
            .collect::<Vec<_>>(),
        ["loop invariant not satisfied"],
        "{result:?}"
    );
}

#[test]
fn assert_forall_array_headers_check_clause_counts_and_unique_calls() {
    let duplicate_requires =
        "only one call to requires allowed (use requires([e1, ..., en]) for multiple expressions";
    let duplicate_ensures =
        "only one call to ensures allowed (use ensures([e1, ..., en]) for multiple expressions";
    for (index, (header, message)) in [
        (
            "requires([true, true]); ensures([true]);",
            "assert_forall_by can have at most one requires",
        ),
        (
            "requires([verus_builtin::constrain_type(0u8, 0u8), true]); ensures([true]);",
            "assert_forall_by can have at most one requires",
        ),
        (
            "ensures([true, true]);",
            "assert_forall_by must have exactly one ensures",
        ),
        (
            "verus_builtin::ensures::<[bool; 0]>([]);",
            "assert_forall_by must have exactly one ensures",
        ),
        (
            "ensures([verus_builtin::constrain_type(0u8, 0u8)]);",
            "assert_forall_by must have exactly one ensures",
        ),
        (
            "requires([true]); requires([true]); ensures([true]);",
            duplicate_requires,
        ),
        (
            "verus_builtin::requires::<[bool; 0]>([]); requires([true]); ensures([true]);",
            duplicate_requires,
        ),
        ("ensures([true]); ensures([true]);", duplicate_ensures),
        (
            "verus_builtin::ensures::<[bool; 0]>([]); ensures([true]);",
            duplicate_ensures,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let source = format!("verus! {{ proof fn test() {{ verus_builtin::assert_forall_by(|| {{ {header} }}); }} }}");
        let result = common::run(&format!("forall_array_cardinality_{index}"), &source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        assert!(
            result.record["crate_refusals"]
                .as_array()
                .unwrap()
                .is_empty(),
            "{result:?}"
        );
        assert_eq!(
            result
                .errors()
                .iter()
                .map(|error| error.message.as_str())
                .collect::<Vec<_>>(),
            [message],
            "{result:?}"
        );
    }
    // Requires does not erase the intrinsic or hide executable arguments.
    for (index, body) in [
        "verus_builtin::assert_forall_by(|| { ensures([effect()]); });",
        "verus_builtin::assert_forall_by(|| { requires([verus_builtin::constrain_type(effect(), true)]); ensures([true]); });",
        "verus_builtin::assert_forall_by(|| { requires([verus_builtin::constrain_type(true, effect())]); ensures([true]); });",
        "requires([verus_builtin::constrain_type(effect(), true)]); ensures([true]);",
        "requires([verus_builtin::constrain_type(true, effect())]); ensures([true]);",
    ].into_iter().enumerate() {
        let source = format!("verus! {{ fn effect() -> bool {{ true }} proof fn test() {{ {body} }} }}");
        let result = common::run(&format!("array_header_exec_member_{index}"), &source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(result.raw.is_empty(), "{result:?}");
        let errors = result.errors();
        assert_eq!(errors.len(), 1, "{result:?}");
        assert!(errors[0].message.starts_with("cannot call function `")
            && errors[0].message.contains("effect")
            && errors[0].message.ends_with("` with mode exec"), "{result:?}");
    }

    // A plain local function with the same spelling is a real clause.
    let source = "verus! { spec fn constrain_type(x: u8, y: u8) -> bool { true } proof fn test() { verus_builtin::assert_forall_by(|| { ensures([true, constrain_type(0u8, 0u8)]); }); } }";
    let result = common::run("forall_ensures_local_typing_aid_spelling", source, &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    assert!(result.raw.is_empty(), "{result:?}");
    assert!(
        result.record["crate_refusals"]
            .as_array()
            .unwrap()
            .is_empty(),
        "{result:?}"
    );
    assert_eq!(
        result
            .errors()
            .iter()
            .map(|error| error.message.as_str())
            .collect::<Vec<_>>(),
        ["assert_forall_by must have exactly one ensures"],
        "{result:?}"
    );
}
