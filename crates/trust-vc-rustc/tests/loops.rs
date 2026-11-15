//! Loops: `while` and `loop` with invariants, `ensures`, `decreases`,
//! `break` and `continue`, with and without isolation. Each program has a
//! twin that differs from it in one line.
//!
//! The programs are in `loops/<name>.rs` and their twins in
//! `loops/<name>.twin.rs`, from the `verus!` line on (line 1), except the
//! whole files of [`RAW`], which set `exec_allows_no_decreases_clause` on the
//! crate as the upstream harness does. Every expected verdict, message and
//! line is that of the reference Verus+z3 run on the same program, except
//! where the expected outcome is a refusal. The binary needs the
//! trustc-built `verus_builtin` crates (see `common`).

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

const END: &str = "invariant not satisfied at end of loop body";
const ENTRY: &str = "invariant not satisfied before loop";
const EXIT: &str = "loop invariant not satisfied";
const ASSERT: &str = "assertion failed";
const POST: &str = "postcondition not satisfied";

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
            program: include_str!(concat!("loops/", $name, ".rs")),
            twin: include_str!(concat!("loops/", $name, ".twin.rs")),
            expect: $expect,
            twin_expect: $twin_expect,
        }
    };
}

const CASES: &[Case] = &[
    // The invariant and the negated condition give what holds after a
    // `while`; the twin's invariant is not preserved.
    case!("basic_while", CHECKED, failed(&[(END, 5)])),
    // An isolated body knows only the invariants: the precondition must be
    // repeated as one.
    case!(
        "isolation_needs_invariant",
        CHECKED,
        failed(&[(ASSERT, 12)])
    ),
    // A loop `ensures` is checked at the `break` and known after the loop.
    case!(
        "break_checks_ensures",
        CHECKED,
        failed(&[(EXIT, 10), (ASSERT, 14)])
    ),
    // Only what the loop assigns is arbitrary after it.
    case!("havoc_assigned_only", CHECKED, failed(&[(ASSERT, 12)])),
    // The measure must decrease at the end of the body and at `continue`.
    case!(
        "decreases_at_end",
        CHECKED,
        failed(&[("decreases not satisfied at end of loop", 4)])
    ),
    case!(
        "decreases_at_continue",
        CHECKED,
        failed(&[("decreases not satisfied at continue", 10)])
    ),
    // A parameter assigned before an isolated loop has an entry value
    // unrelated to its current one inside the loop.
    case!("param_modified_before_loop", CHECKED, failed(&[(POST, 3)])),
    // Without isolation the paths that break join after the loop, and the
    // body sees what held before the loop.
    case!("joined_break_paths", CHECKED, failed(&[(ASSERT, 14)])),
    case!("joined_sees_context", CHECKED, failed(&[(ASSERT, 11)])),
    // A loop needs a measure unless the crate allows it.
    case!(
        "decreases_required",
        rejected(&[("loop must have a decreases clause", 4)]),
        CHECKED
    ),
    case!("invariant_on_entry", CHECKED, failed(&[(ENTRY, 5)])),
    case!("invariant_at_end", CHECKED, failed(&[(END, 5)])),
    // The condition's checks run before every iteration and after the
    // last; Verus reports the failure once.
    case!(
        "condition_overflow",
        CHECKED,
        failed(&[("possible arithmetic underflow/overflow", 4)])
    ),
    // An inner loop's body knows only its own invariants.
    case!("nested_isolation", CHECKED, failed(&[(ASSERT, 15)])),
    case!("loop_then_return", CHECKED, failed(&[(POST, 4)])),
    // A condition with statements.
    case!("condition_block", CHECKED, failed(&[(ASSERT, 14)])),
    // `break 'x` from an inner loop checks the outer loop's invariants.
    case!("break_outer_loop", failed(&[(EXIT, 30)]), CHECKED),
    case!(
        "loop_in_proof",
        rejected(&[("cannot use while in proof or spec mode", 4)]),
        CHECKED
    ),
    case!(
        "joined_except_break",
        rejected(&[(
            "loop invariants with 'loop_isolation(false)' cannot be invariant_except_break",
            5
        )]),
        CHECKED
    ),
    // Verus's error for a `continue` in a labeled isolated loop with a
    // measure is not reproduced.
    case!(
        "labeled_continue",
        ("refused", &[("trust-vc refused: loop-continue-label:", 9)]),
        CHECKED
    ),
    // A `while` with a `break` knows nothing of its condition after it.
    case!("while_break_converts", failed(&[(ASSERT, 10)]), CHECKED),
    // A `return` inside a loop, through a `&mut` parameter.
    case!("return_in_loop", CHECKED, failed(&[(POST, 23)])),
    // Verus keeps the statements after a `break;` or `continue;` statement:
    // they are unreachable, but what they assign is modified by the loop,
    // and a loop among them has its body checked. The twin replaces the
    // assignment with a `let` or the failing assertion with a true one.
    case!("dead_assign_after_break", failed(&[(ASSERT, 10)]), CHECKED),
    case!("dead_param_after_break", failed(&[(POST, 3)]), CHECKED),
    case!("dead_loop_after_continue", failed(&[(ASSERT, 14)]), CHECKED),
    // `{ break; };` keeps the statements after it; `{ break; }`, which
    // rustc coerces from `!`, ends the block.
    case!("dead_after_block_break", failed(&[(ASSERT, 10)]), CHECKED),
    // Without isolation, a path that breaks inside a nested `if` is not on
    // the path that goes on after the `if`: what is learnt there does not
    // constrain it.
    case!("joined_nested_break", failed(&[(POST, 4)]), CHECKED),
    case!(
        "joined_nested_break_assume",
        failed(&[(ASSERT, 14)]),
        CHECKED
    ),
    // A branch whose loop never exits does not reach the code after the
    // `if`.
    case!("joined_infinite_branch", CHECKED, failed(&[(ASSERT, 11)])),
    // Nor does a loop without isolation that never exits.
    case!("joined_never_exits", CHECKED, failed(&[(POST, 5)])),
    // Unreachable code without a loop has no effect on the checks, so what
    // it holds is not read.
    case!(
        "dead_unsupported_after_break",
        CHECKED,
        failed(&[(ASSERT, 10)])
    ),
];

/// Whole files: their prelude sets `exec_allows_no_decreases_clause`.
const RAW: &[&str] = &["break_outer_loop", "return_in_loop"];

/// The number of lines in which two programs differ.
fn differing_lines(a: &str, b: &str) -> usize {
    let (a, b): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if a.len() != b.len() {
        return usize::MAX;
    }
    a.iter().zip(&b).filter(|(x, y)| x != y).count()
}

fn check(name: &str, program: &str, raw: bool, (outcome, want): Expect) -> Vec<String> {
    let run = if raw {
        common::run_raw(name, program, &[])
    } else {
        common::run(name, program, &[])
    };
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
fn loops_and_their_twins() {
    let mut problems = Vec::new();
    for case in CASES {
        assert_eq!(
            differing_lines(case.program, case.twin),
            1,
            "{}: the twin is not a one-line change",
            case.name
        );
        let raw = RAW.contains(&case.name);
        problems.extend(check(case.name, case.program, raw, case.expect));
        let twin = format!("{}__twin", case.name);
        problems.extend(check(&twin, case.twin, raw, case.twin_expect));
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}
