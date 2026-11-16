//! Verus's rejections that the reader reproduces, and the refusals that stand
//! in for rules it does not, each with a liar twin.
//!
//! Every case is a program Verus rejects (or that trust-vc must refuse) and a
//! twin that differs from it in one line (or, for an option, only in the
//! options) with the verdict Verus gives the twin. The expected messages and
//! lines are those of the reference Verus+z3 run on the same programs. The
//! binary needs the trustc-built `verus_builtin` crates (see `common`).

mod common;

/// What a run must produce: its outcome and its errors, as message prefixes
/// and the line of their first primary span (1 is the `verus!` line).
struct Expect {
    outcome: &'static str,
    errors: &'static [(&'static str, usize)],
}

const CHECKED: Expect = Expect {
    outcome: "checked",
    errors: &[],
};

struct Case {
    name: &'static str,
    program: &'static str,
    args: &'static [&'static str],
    expect: Expect,
    twin: &'static str,
    twin_args: &'static [&'static str],
    twin_expect: Expect,
}

const fn rejected(
    name: &'static str,
    program: &'static str,
    errors: &'static [(&'static str, usize)],
    twin: &'static str,
) -> Case {
    Case {
        name,
        program,
        args: &[],
        expect: Expect {
            outcome: "verus-rejected",
            errors,
        },
        twin,
        twin_args: &[],
        twin_expect: CHECKED,
    }
}

const CASES: &[Case] = &[
    Case {
        name: "old_in_spec_signature",
        program: "verus! {\nspec fn foo(x: &mut u64) -> u64\n    recommends *old(x) == 0,\n{ 0 }\n}\n",
        args: &["-V", "new-mut-ref"],
        expect: Expect {
            outcome: "verus-rejected",
            errors: &[("`old` is meaningless in spec functions", 3)],
        },
        twin: "verus! {\nspec fn foo(x: &mut u64) -> u64\n    recommends *x == 0,\n{ 0 }\n}\n",
        twin_args: &["-V", "new-mut-ref"],
        twin_expect: CHECKED,
    },
    Case {
        name: "old_in_spec_body",
        program: "verus! {\nspec fn foo(x: &mut u64) -> u64 {\n    *old(x)\n}\n}\n",
        args: &["-V", "new-mut-ref"],
        expect: Expect {
            outcome: "verus-rejected",
            errors: &[("`old` is meaningless in spec functions", 3)],
        },
        twin: "verus! {\nspec fn foo(x: &mut u64) -> u64 {\n    *x\n}\n}\n",
        twin_args: &["-V", "new-mut-ref"],
        twin_expect: CHECKED,
    },
    Case {
        name: "old_uses_resolved_builtin_identity",
        program: "verus! {\nspec fn old(n: u64) -> u64 { n }\nspec fn foo(x: &mut u64) -> u64 {\n    *verus_builtin::old(x)\n}\n}\n",
        args: &["-V", "new-mut-ref"],
        expect: Expect {
            outcome: "verus-rejected",
            errors: &[("`old` is meaningless in spec functions", 4)],
        },
        twin: "verus! {\nspec fn old(n: u64) -> u64 { n }\nspec fn foo(x: &mut u64) -> u64 {\n    self::old(*x)\n}\n}\n",
        twin_args: &["-V", "new-mut-ref"],
        twin_expect: CHECKED,
    },
    // Header rules (rust_to_vir_func.rs), at the signature.
    rejected(
        "spec_requires",
        "verus! {\nspec fn s(x: int) -> int\n    requires x > 0,\n{ x }\n}\n",
        &[("spec functions cannot have requires/ensures", 2)],
        "verus! {\nspec fn s(x: int) -> int\n    recommends x > 0,\n{ x }\n}\n",
    ),
    rejected(
        "spec_ensures",
        "verus! {\nspec fn s(x: int) -> (r: int)\n    ensures r == x,\n{ x }\n}\n",
        &[("spec functions cannot have requires/ensures", 2)],
        "verus! {\nproof fn s(x: int) -> (r: int)\n    ensures r == x,\n{ x }\n}\n",
    ),
    rejected(
        "proof_recommends",
        "verus! {\nproof fn f(x: int)\n    recommends x > 0,\n{ }\n}\n",
        &[("non-spec functions cannot have recommends", 2)],
        "verus! {\nproof fn f(x: int)\n    requires x > 0,\n{ }\n}\n",
    ),
    rejected(
        "unnamed_return",
        "verus! {\nfn f() -> u64\n    ensures true,\n{ 5 }\n}\n",
        &[(
            "the return value must be named in a function with an ensures clause",
            2,
        )],
        "verus! {\nfn f() -> (r: u64)\n    ensures true,\n{ 5 }\n}\n",
    ),
    rejected(
        "spec_no_value",
        "verus! {\nspec fn s(x: u64) { }\n}\n",
        &[("expected pure mathematical expression", 2)],
        "verus! {\nspec fn s(x: u64) { () }\n}\n",
    ),
    rejected(
        "opaque_bodyless",
        "verus! {\n#[verifier::opaque]\nuninterp spec fn s(x: int) -> bool;\n}\n",
        &[("opaque has no effect on a function without a body", 3)],
        "verus! {\n#[verifier::opaque]\nspec fn s(x: int) -> bool { true }\n}\n",
    ),
    rejected(
        "opaque_proof",
        "verus! {\n#[verifier::opaque]\nproof fn p() { }\n}\n",
        &[(
            "function is marked `opaque` but it is not a `spec` function",
            3,
        )],
        "verus! {\n#[verifier::rlimit(10)]\nproof fn p() { }\n}\n",
    ),
    // Well-formedness (well_formed.rs): the first error only.
    rejected(
        "open_refers_private",
        "verus! {\nspec fn f() -> int { 1 }\npub open spec fn g() -> int { f() }\n}\n",
        &[(
            "in pub open spec function, cannot refer to private function",
            3,
        )],
        "verus! {\npub open spec fn f() -> int { 1 }\npub open spec fn g() -> int { f() }\n}\n",
    ),
    rejected(
        "pub_requires_private",
        "verus! {\nspec fn f(x: u64) -> bool { x > 0 }\npub fn g(x: u64)\n    requires f(x),\n{ }\n}\n",
        &[(
            "in 'requires' clause of public function, cannot refer to private function",
            4,
        )],
        "verus! {\nspec fn f(x: u64) -> bool { x > 0 }\nfn g(x: u64)\n    requires f(x),\n{ }\n}\n",
    ),
    rejected(
        "pub_ensures_private",
        "verus! {\nspec fn f(x: u64) -> bool { x >= 0 }\npub fn g(x: u64)\n    ensures f(x),\n{ }\n}\n",
        &[(
            "in 'ensures' clause of public function, cannot refer to private function",
            4,
        )],
        "verus! {\npub open spec fn f(x: u64) -> bool { x >= 0 }\npub fn g(x: u64)\n    ensures f(x),\n{ }\n}\n",
    ),
    rejected(
        "pub_requires_private_field",
        "verus! {\npub struct S { x: u64 }\npub fn g(s: S)\n    requires s.x > 0,\n{ }\n}\n",
        &[("disallowed: field expression for an opaque datatype", 4)],
        "verus! {\npub struct S { pub x: u64 }\npub fn g(s: S)\n    requires s.x > 0,\n{ }\n}\n",
    ),
    rejected(
        "field_other_module",
        "verus! {\nmod m {\n    pub struct S { pub x: u64, y: u64 }\n}\nfn g(s: m::S) -> u64 { s.x }\n}\n",
        &[("disallowed: field expression for an opaque datatype", 5)],
        "verus! {\nmod m {\n    pub struct S { pub x: u64, pub y: u64 }\n}\nfn g(s: m::S) -> u64 { s.x }\n}\n",
    ),
    rejected(
        "non_visible_datatype",
        "verus! {\nstruct S { pub x: u64 }\npub(crate) fn g(s: S)\n    requires s.x > 0,\n{ }\npub proof fn h(s: S)\n    requires s.x > 0,\n{ }\n}\n",
        &[("disallowed: field expression for a non-visible datatype", 7)],
        "verus! {\nstruct S { pub x: u64 }\npub(crate) fn g(s: S)\n    requires s.x > 0,\n{ }\nproof fn h(s: S)\n    requires s.x > 0,\n{ }\n}\n",
    ),
    rejected(
        "reveal_uninterp",
        "verus! {\nuninterp spec fn s(x: int) -> bool;\nproof fn f() { reveal(s); }\n}\n",
        &[(
            "reveal/fuel statement is not allowed here because the function `test_crate::s` is marked 'closed'",
            3,
        )],
        "verus! {\nspec fn s(x: int) -> bool { true }\nproof fn f() { reveal(s); }\n}\n",
    ),
    rejected(
        "reveal_closed_other_module",
        "verus! {\nmod m {\n    pub closed spec fn foo(u: u64) -> u64 { u }\n}\nproof fn q() {\n    reveal(m::foo);\n}\n}\n",
        &[(
            "reveal/fuel statement is not allowed here because the function `test_crate::m::foo` is marked 'closed'",
            6,
        )],
        "verus! {\nmod m {\n    pub open spec fn foo(u: u64) -> u64 { u }\n}\nproof fn q() {\n    reveal(m::foo);\n}\n}\n",
    ),
    rejected(
        "reveal_with_fuel_without_decreases",
        "verus! {\n#[verifier::opaque]\nspec fn f() -> bool { true }\nproof fn p() { reveal_with_fuel(f, 2); }\n}\n",
        &[(
            "reveal_with_fuel statements require a spec function with a decreases clause",
            4,
        )],
        "verus! {\n#[verifier::opaque]\nspec fn f() -> bool { true }\nproof fn p() { reveal(f); }\n}\n",
    ),
    rejected(
        "main_proof",
        "verus! {\npub proof fn main() { }\n}\n",
        &[("`main` function should be #[verifier::exec]", 2)],
        "verus! {\npub fn main() { }\n}\n",
    ),
    // One error per phase after VIR is built: two functions break the same
    // rule, Verus reports the first.
    Case {
        name: "well_formed_reports_one_error",
        program: "verus! {\nspec fn f() -> int { 1 }\npub open spec fn g() -> int { f() }\npub open spec fn h() -> int { f() }\n}\n",
        args: &[],
        expect: Expect {
            outcome: "verus-rejected",
            errors: &[(
                "in pub open spec function, cannot refer to private function",
                3,
            )],
        },
        twin: "verus! {\nspec fn f() -> int { 1 }\npub closed spec fn g() -> int { f() }\npub open spec fn h() -> int { f() }\n}\n",
        twin_args: &[],
        twin_expect: Expect {
            outcome: "verus-rejected",
            errors: &[(
                "in pub open spec function, cannot refer to private function",
                4,
            )],
        },
    },
    // Well-formedness comes before the mode check.
    Case {
        name: "well_formed_before_modes",
        program: "verus! {\nspec fn f(x: u64) -> bool { x > 0 }\npub fn g(x: u64)\n    requires f(x),\n{ }\nfn h() { let x: u64 = 1; proof { x = 2; } }\n}\n",
        args: &[],
        expect: Expect {
            outcome: "verus-rejected",
            errors: &[(
                "in 'requires' clause of public function, cannot refer to private function",
                4,
            )],
        },
        twin: "verus! {\nspec fn f(x: u64) -> bool { x > 0 }\nfn g(x: u64)\n    requires f(x),\n{ }\nfn h() { let x: u64 = 1; proof { x = 2; } }\n}\n",
        twin_args: &[],
        twin_expect: Expect {
            outcome: "verus-rejected",
            errors: &[("cannot assign to exec variable from proof mode", 6)],
        },
    },
    // A labelled `ensures` clause is not assumed by callers.
    Case {
        name: "labelled_ensures_proof_note",
        program: "verus! {\nproof fn g(a: int) -> (r: int)\n    ensures\n        #![verifier::proof_note(\"n\")]\n        r == a,\n{ a }\nproof fn f() { let x = g(1); assert(x == 1); }\n}\n",
        args: &[],
        expect: Expect {
            outcome: "verification-failed",
            errors: &[("assertion failed", 7)],
        },
        twin: "verus! {\nproof fn g(a: int) -> (r: int)\n    ensures\n        \n        r == a,\n{ a }\nproof fn f() { let x = g(1); assert(x == 1); }\n}\n",
        twin_args: &[],
        twin_expect: CHECKED,
    },
    Case {
        name: "labelled_ensures_custom_err",
        program: "verus! {\nfn g(a: u64) -> (r: u64)\n    ensures\n        #![verifier::custom_err(\"c\")]\n        r == a,\n{ a }\nfn f() { let x = g(1); assert(x == 1); }\n}\n",
        args: &[],
        expect: Expect {
            outcome: "verification-failed",
            errors: &[("assertion failed", 7)],
        },
        twin: "verus! {\nfn g(a: u64) -> (r: u64)\n    ensures\n        \n        r == a,\n{ a }\nfn f() { let x = g(1); assert(x == 1); }\n}\n",
        twin_args: &[],
        twin_expect: CHECKED,
    },
    // Refusals for what Verus fails on or the reader does not reproduce.
    Case {
        name: "hide_without_body",
        program: "verus! {\nuninterp spec fn s(x: int) -> bool;\nproof fn f() { hide(s); }\n}\n",
        args: &[],
        expect: Expect {
            outcome: "refused",
            errors: &[("trust-vc refused: hide-target:", 3)],
        },
        twin: "verus! {\nspec fn s(x: int) -> bool { true }\nproof fn f() { hide(s); }\n}\n",
        twin_args: &[],
        twin_expect: CHECKED,
    },
    Case {
        name: "no_verify",
        program: "verus! {\nproof fn f() { assert(true); }\n}\n",
        args: &["--no-verify"],
        expect: Expect {
            outcome: "refused",
            errors: &[("trust-vc refused: no-verify:", 2)],
        },
        twin: "verus! {\nproof fn f() { assert(true); }\n}\n",
        twin_args: &[],
        twin_expect: CHECKED,
    },
];

/// The lines where two programs differ.
fn differing_lines(a: &str, b: &str) -> usize {
    let (a, b): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
    if a.len() != b.len() {
        return usize::MAX;
    }
    a.iter().zip(&b).filter(|(x, y)| x != y).count()
}

fn check(name: &str, program: &str, args: &[&str], expect: &Expect) -> Vec<String> {
    let run = common::run(name, program, args);
    let mut problems = Vec::new();
    if run.outcome() != expect.outcome {
        problems.push(format!(
            "{name}: outcome {} instead of {}",
            run.outcome(),
            expect.outcome
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
    let matches = errors.len() == expect.errors.len()
        && errors
            .iter()
            .zip(expect.errors)
            .all(|((message, line), (want, want_line))| {
                message.starts_with(want) && line == want_line
            });
    if !matches {
        problems.push(format!(
            "{name}: errors {errors:?} instead of {:?}",
            expect.errors
        ));
    }
    if !run.raw.is_empty() {
        problems.push(format!("{name}: non-JSON stderr {:?}", run.raw));
    }
    if expect.outcome == "checked" && run.exit != 0 {
        problems.push(format!("{name}: exit {} for a checked run", run.exit));
    }
    problems
}

#[test]
fn verus_rules_and_their_twins() {
    let mut problems = Vec::new();
    for case in CASES {
        let changed = differing_lines(case.program, case.twin);
        let one_change = if case.args == case.twin_args {
            changed == 1
        } else {
            changed == 0
        };
        assert!(
            one_change,
            "{}: the twin is not a one-line change",
            case.name
        );
        problems.extend(check(case.name, case.program, case.args, &case.expect));
        let twin = format!("{}__twin", case.name);
        problems.extend(check(&twin, case.twin, case.twin_args, &case.twin_expect));
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

#[test]
fn proof_and_exec_old_keep_their_original_values() {
    for (label, mode) in [("proof", "proof fn"), ("exec", "fn")] {
        let source = format!(
            "verus! {{ {mode} preserve_old(x: &mut u64) {{ assert(*old(x) == *old(x)); }} }}"
        );
        let positive = common::run(&format!("old_preserved_{label}"), &source, &[]);
        assert_eq!(positive.outcome(), "checked", "{positive:?}");
        assert_eq!(positive.exit, 0, "{positive:?}");
        assert!(positive.errors().is_empty(), "{positive:?}");
        let negative = source.replace("==", "!=");
        let negative = common::run(&format!("old_preserved_{label}_false"), &negative, &[]);
        assert_eq!(negative.outcome(), "verification-failed", "{negative:?}");
        assert_eq!(negative.errors().len(), 1, "{negative:?}");
        assert_eq!(
            negative.errors()[0].message,
            "assertion failed",
            "{negative:?}"
        );
    }
}
