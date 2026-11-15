//! Termination: `decreases` on recursive spec, proof and exec functions,
//! mutual recursion, fuel, `when`, `decreases_by`, proof blocks in spec
//! code, and the errors Verus reports for them. Each program has a twin
//! that differs from it in one line.
//!
//! The programs are in `termination/<name>.rs` and their twins in
//! `termination/<name>.twin.rs`, from the `verus!` line on (line 1). Every
//! expected verdict, message and line is that of the reference Verus+z3
//! run on the same program. The binary needs the trustc-built
//! `verus_builtin` crates (see `common`).

mod common;

#[path = "termination/recursive_result_types.rs"]
mod recursive_result_types;

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

const TERMINATION: &str = "could not prove termination";
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
            program: include_str!(concat!("termination/", $name, ".rs")),
            twin: include_str!(concat!("termination/", $name, ".twin.rs")),
            expect: $expect,
            twin_expect: $twin_expect,
        }
    };
}

const CASES: &[Case] = &[
    // A recursive call must decrease the measure; the twin's does not.
    case!("spec_decreases", CHECKED, failed(&[(TERMINATION, 5)])),
    case!("proof_decreases", CHECKED, failed(&[(TERMINATION, 6)])),
    case!("exec_decreases", CHECKED, failed(&[(TERMINATION, 9)])),
    // A spec function returning `()` is checked too.
    case!("unit_spec", CHECKED, failed(&[(TERMINATION, 6)])),
    // `decreases j, k` is lexicographic.
    case!("lexicographic", CHECKED, failed(&[(TERMINATION, 6)])),
    // A call unfolds once around its cycle (two functions here): the twin
    // needs one unfolding more.
    case!("mutual_fuel", CHECKED, failed(&[(ASSERT, 15)])),
    // `reveal_with_fuel(f, 2)` unfolds a self-recursive function twice; the
    // twin's fuel 1 unfolds it once.
    case!("reveal_with_fuel", CHECKED, failed(&[(ASSERT, 10)])),
    // `when` is assumed by the termination check...
    case!("decreases_when", CHECKED, failed(&[(TERMINATION, 6)])),
    // ... and guards the definition.
    case!("when_guards_definition", CHECKED, failed(&[(ASSERT, 10)])),
    // The `decreases_by` function's body is walked first.
    case!("decreases_by", CHECKED, failed(&[(TERMINATION, 14)])),
    // A proof block in spec code is walked where it stands.
    case!("proof_in_spec", CHECKED, failed(&[(TERMINATION, 19)])),
    // `decreases_to!` on integers, lexicographic.
    case!("decreases_to", CHECKED, failed(&[(ASSERT, 5)])),
    // Chained comparisons.
    case!("chained", CHECKED, failed(&[(ASSERT, 5)])),
    // A failing termination check is not assumed after it: Verus reports
    // each failing call.
    case!(
        "two_failing_calls",
        failed(&[(TERMINATION, 6), (TERMINATION, 7)]),
        failed(&[(TERMINATION, 7)])
    ),
    // A body Verus shows only in its module is hidden from the functions of
    // other modules; the twin asserts what holds without it.
    case!("closed_body_other_module", failed(&[(ASSERT, 17)]), CHECKED),
    // Verus's errors.
    case!(
        "second_decreases",
        rejected(&[("only one decreases expression currently supported", 5)]),
        CHECKED
    ),
    // An `external_body` function's `decreases_by` is not read, so the
    // `decreases_by` function is unused.
    case!(
        "external_body_via",
        rejected(&[(
            "function cannot be marked #[verifier::decreases_by] or #[verifier::recommends_by] unless",
            11
        )]),
        CHECKED
    ),
    case!(
        "missing_decreases",
        rejected(&[("recursive function must have a decreases clause", 2)]),
        CHECKED
    ),
    case!(
        "by_not_marked",
        rejected(&[(
            "proof function must be marked #[verifier::decreases_by] or #[verifier::recommends_by]",
            9
        )]),
        CHECKED
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
fn termination_and_its_twins() {
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
