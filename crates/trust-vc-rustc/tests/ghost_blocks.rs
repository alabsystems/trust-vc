//! Proof blocks wherever they appear, each program with a twin that differs
//! from it in one line.
//!
//! A `proof { .. }` block is ghost code: it is erased at run time. When it
//! stands for a value (the tail of a block or an `if` branch, a `let`
//! initializer, a call argument), it is still ghost code, so an assignment to
//! an exec variable inside it is Verus's mode error, not an exec effect. The
//! first ten cases are the programs that showed the hole: each was verified
//! although the assignment it relied on is erased.
//!
//! Every expected verdict, message and line is that of the reference
//! Verus+z3 run on the same program. Lines count from the `verus!` line. The
//! binary needs the trustc-built `verus_builtin` crates (see `common`).

mod common;

const ASSIGN: &str = "cannot assign to exec variable from proof mode";
const NOT_UNIT: &str = "proof block must have type ()";
const CALL_R: &str = "cannot call function `test_crate::r` with mode exec";
const POST: &str = "postcondition not satisfied";
const PROOF_IN_SPEC: &str =
    "proof blocks inside spec code is currently supported only for spec functions with decreases";

/// A run's outcome and its errors, as message prefixes and the line of their
/// first primary span.
type Expect = (&'static str, &'static [(&'static str, usize)]);

const CHECKED: Expect = ("checked", &[]);

const fn rejected(errors: &'static [(&'static str, usize)]) -> Expect {
    ("verus-rejected", errors)
}

const fn failed(errors: &'static [(&'static str, usize)]) -> Expect {
    ("verification-failed", errors)
}

/// Refused for a ghost block on line 2.
const GHOST_BLOCK_REFUSED: Expect = ("refused", &[("trust-vc refused: ghost-block:", 2)]);

struct Case {
    name: &'static str,
    program: &'static str,
    expect: Expect,
    twin: &'static str,
    twin_expect: Expect,
}

const CASES: &[Case] = &[
    // The hunt's programs: an exec assignment in a proof block that ends an
    // `if` branch or a `let` initializer.
    Case {
        name: "assign_unit_call_in_branch",
        program: "verus! {\nspec fn foo() -> bool { true }\n\nfn returns_unit() ensures foo() { }\n\nfn test(b: bool) {\n    let x: ();\n    if b {\n        proof { x = returns_unit(); }\n    }\n}\n}\n",
        expect: rejected(&[(ASSIGN, 9)]),
        twin: "verus! {\nspec fn foo() -> bool { true }\n\nfn returns_unit() ensures foo() { }\n\nfn test(b: bool) {\n    let x: ();\n    if b {\n        x = returns_unit();\n    }\n}\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "assign_unit_in_branch",
        program: "verus! {\nfn test(b: bool) { let x: (); if b { proof { x = (); } } }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool) { let x: (); if b { x = (); } }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "assign_u64_in_branch",
        program: "verus! {\nfn test(b: bool) { let mut x: u64 = 0; if b { proof { x = 1; } } }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool) { let mut x: u64 = 0; if b { proof { assert(x == 0); } } }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "result_from_then_branch",
        program: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; if b { proof { x = 1; } } else { x = 1; } x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; if b { x = 1; } else { x = 1; } x }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "result_from_else_branch",
        program: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; if b { x = 1; } else { proof { x = 1; } } x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; if b { x = 1; } else { proof { assert(x == 0); } } x }\n}\n",
        twin_expect: failed(&[(POST, 2)]),
    },
    Case {
        name: "nested_branch",
        program: "verus! {\nfn test(b: bool, c: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 1; if b { if c { proof { x = 1; } } } x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool, c: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 1; if b { if c { proof { assert(x == 1); } } } x }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "field_in_branch",
        program: "verus! {\nfn test(b: bool) -> (r: (u64, u64)) ensures r.0 == 1 { let mut x: (u64, u64) = (1, 0); if b { proof { x.0 = 1; } } x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool) -> (r: (u64, u64)) ensures r.0 == 1 { let mut x: (u64, u64) = (1, 0); if b { x.0 = 1; } x }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "mut_ref_in_branch",
        program: "verus! {\nfn test(b: bool, p: &mut u64) ensures *p == 1 { *p = 1; if b { proof { *p = 1; } } }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool, p: &mut u64) ensures *p == 1 { *p = 1; if b { *p = 1; } }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "let_init_block",
        program: "verus! {\nfn test() -> (r: u64) ensures r == 1 { let mut x: u64 = 0; let u = { proof { x = 1; } }; x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test() -> (r: u64) ensures r == 1 { let mut x: u64 = 0; let u = { x = 1; }; x }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "let_init_if",
        program: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; let u = if b { proof { x = 1; } } else { x = 1; }; x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; let u = if b { proof { assert(x == 0); } } else { x = 1; }; x }\n}\n",
        twin_expect: failed(&[(POST, 2)]),
    },
    // Other value positions.
    Case {
        name: "let_init_direct",
        program: "verus! {\nfn test() -> (r: u64) ensures r == 1 { let mut x: u64 = 0; let u = proof { x = 1; }; x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test() -> (r: u64) ensures r == 1 { let mut x: u64 = 1; let u = proof { assert(x == 1); }; x }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "call_argument",
        program: "verus! {\nfn e(u: ()) { }\nfn test() { let mut x: u64 = 0; e(proof { x = 1; }); }\n}\n",
        expect: rejected(&[(ASSIGN, 3)]),
        twin: "verus! {\nfn e(u: ()) { }\nfn test() { let mut x: u64 = 0; e(proof { assert(x == 0); }); }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "and_right_side",
        program: "verus! {\nfn test(b: bool) -> (r: bool) ensures r == b { let mut x: u64 = 0; b && { proof { x = 1; } true } }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool) -> (r: bool) ensures r == b { let mut x: u64 = 0; b && { proof { assert(x == 1); } true } }\n}\n",
        twin_expect: failed(&[("assertion failed", 2)]),
    },
    Case {
        name: "call_value_in_branch",
        program: "verus! {\nfn r() -> u64 { 1 }\nfn test(b: bool) { let mut x: u64 = 0; if b { proof { x = r(); } } }\n}\n",
        expect: rejected(&[(ASSIGN, 3)]),
        twin: "verus! {\nfn r() -> u64 { 1 }\nfn test(b: bool) { let mut x: u64 = 0; if b { x = r(); } }\n}\n",
        twin_expect: CHECKED,
    },
    // Proof code in a value-position proof block is proof code.
    Case {
        name: "proof_call_in_branch",
        program: "verus! {\nproof fn l() ensures true { }\nfn test(b: bool) { if b { proof { l(); } } }\n}\n",
        expect: CHECKED,
        twin: "verus! {\nproof fn l() requires false { }\nfn test(b: bool) { if b { proof { l(); } } }\n}\n",
        twin_expect: failed(&[("precondition not satisfied", 3)]),
    },
    Case {
        name: "ghost_arithmetic_in_branch",
        program: "verus! {\nfn test(b: bool, x: u64) { if b { proof { let y = x + 1; assert(y > x); } } }\n}\n",
        expect: CHECKED,
        twin: "verus! {\nfn test(b: bool, x: u64) { if b { let y = x + 1; } }\n}\n",
        twin_expect: failed(&[("possible arithmetic underflow/overflow", 2)]),
    },
    // The attribute spelling `verus::internal(proof_block)`.
    Case {
        name: "internal_spelling_value",
        program: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; if b { #[verus::internal(proof_block)] { x = 1; } } else { x = 1; } x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; if b { #[verus::internal(proof_block)] { let y: u64 = 1; } } else { x = 1; } x }\n}\n",
        twin_expect: failed(&[(POST, 2)]),
    },
    Case {
        name: "internal_spelling_statement",
        program: "verus! {\nfn test() -> (r: u64) ensures r == 1 { let mut x: u64 = 0; #[verus::internal(proof_block)] { x = 1; } x }\n}\n",
        expect: rejected(&[(ASSIGN, 2)]),
        twin: "verus! {\nfn test() -> (r: u64) ensures r == 1 { let mut x: u64 = 0; #[verus::internal(proof_block)] { let y: u64 = 1; } x }\n}\n",
        twin_expect: failed(&[(POST, 2)]),
    },
    // A proof block's type must be ().
    Case {
        name: "statement_of_type_u64",
        program: "verus! {\nfn test() { proof { 5u64 }; }\n}\n",
        expect: rejected(&[(NOT_UNIT, 2)]),
        twin: "verus! {\nfn test() { proof { () }; }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "statement_of_type_bool",
        program: "verus! {\nfn test(x: u64) { proof { x == 1 }; }\n}\n",
        expect: rejected(&[(NOT_UNIT, 2)]),
        twin: "verus! {\nfn test(x: u64) { proof { assert(x == x); }; }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "let_init_of_type_u64",
        program: "verus! {\nfn test() { let v = proof { 5u64 }; }\n}\n",
        expect: rejected(&[(NOT_UNIT, 2)]),
        twin: "verus! {\nfn test() { let v = proof { () }; }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "branch_of_type_u64",
        program: "verus! {\nfn test(b: bool) -> (r: u64) { if b { proof { 5u64 } } else { 1 } }\n}\n",
        expect: rejected(&[(NOT_UNIT, 2)]),
        twin: "verus! {\nfn test(b: bool) -> (r: u64) { if b { 5u64 } else { 1 } }\n}\n",
        twin_expect: CHECKED,
    },
    // `verus!` marks a proof block in proof code as a proof block in spec
    // code, which only a spec function with `decreases` may hold.
    Case {
        name: "proof_block_in_proof_fn",
        program: "verus! {\nproof fn test(b: bool) { if b { proof { } } }\n}\n",
        expect: rejected(&[(PROOF_IN_SPEC, 2)]),
        twin: "verus! {\nproof fn test(b: bool) { if b { } }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "proof_block_in_proof_block",
        program: "verus! {\nfn test(b: bool) { proof { if b { proof { } } } }\n}\n",
        expect: rejected(&[(PROOF_IN_SPEC, 2)]),
        twin: "verus! {\nfn test(b: bool) { proof { if b { } } }\n}\n",
        twin_expect: CHECKED,
    },
    // A tracked block, which the reader does not read, is refused in value
    // position too. Verus rejects the program.
    Case {
        name: "tracked_block_in_branch",
        program: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; if b { #[verifier::tracked_block] { x = 1; } } else { x = 1; } x }\n}\n",
        expect: GHOST_BLOCK_REFUSED,
        twin: "verus! {\nfn test(b: bool) -> (r: u64) ensures r == 1 { let mut x: u64 = 0; if b { { x = 1; } } else { x = 1; } x }\n}\n",
        twin_expect: CHECKED,
    },
    // Mode errors come in source order: an assignment's target before its
    // value, a call before its arguments.
    Case {
        name: "order_target_before_call",
        program: "verus! {\nfn r() -> u64 { 1 }\nfn test() { let mut x: u64 = 0; proof { x = r(); } }\n}\n",
        expect: rejected(&[(ASSIGN, 3)]),
        twin: "verus! {\nfn r() -> u64 { 1 }\nfn test() { let mut x: u64 = 0; proof { let y = r(); } }\n}\n",
        twin_expect: rejected(&[(CALL_R, 3)]),
    },
    Case {
        name: "order_target_before_unit_call",
        program: "verus! {\nfn r() { }\nfn test() { let x: (); proof { x = r(); } }\n}\n",
        expect: rejected(&[(ASSIGN, 3)]),
        twin: "verus! {\nfn r() { }\nfn test() { let x: (); proof { r(); } }\n}\n",
        twin_expect: rejected(&[(CALL_R, 3)]),
    },
    Case {
        name: "order_deref_target_before_call",
        program: "verus! {\nfn r() -> u64 { 1 }\nfn test(p: &mut u64) { proof { *p = r(); } }\n}\n",
        expect: rejected(&[(ASSIGN, 3)]),
        twin: "verus! {\nfn r() -> u64 { 1 }\nfn test(p: &mut u64) { *p = r(); }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "order_field_target_before_call",
        program: "verus! {\nfn r() -> u64 { 1 }\nfn test() { let mut x: (u64, u64) = (0, 0); proof { x.0 = r(); } }\n}\n",
        expect: rejected(&[(ASSIGN, 3)]),
        twin: "verus! {\nfn r() -> u64 { 1 }\nfn test() { let mut x: (u64, u64) = (0, 0); x.0 = r(); }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "order_compound_target_before_call",
        program: "verus! {\nfn r() -> u64 { 1 }\nfn test() { let mut x: u64 = 0; proof { x += r(); } }\n}\n",
        expect: rejected(&[(ASSIGN, 3)]),
        twin: "verus! {\nfn r() -> u64 { 1 }\nfn test() { let mut x: u64 = 0; x += r(); }\n}\n",
        twin_expect: CHECKED,
    },
    Case {
        name: "order_call_before_arguments",
        program: "verus! {\nfn r(a: u64) -> u64 { a }\nfn q(a: u64) -> u64 { a }\nfn test() { proof { let y = r(q(1)); } }\n}\n",
        expect: rejected(&[(CALL_R, 4)]),
        twin: "verus! {\nfn r(a: u64) -> u64 { a }\nfn q(a: u64) -> u64 { a }\nfn test() { proof { let y = q(r(1)); } }\n}\n",
        twin_expect: rejected(&[("cannot call function `test_crate::q` with mode exec", 4)]),
    },
    Case {
        name: "order_statements",
        program: "verus! {\nfn r() -> u64 { 1 }\nfn test() { let mut x: u64 = 0; proof {\n    let y = r();\n    x = 1;\n} }\n}\n",
        expect: rejected(&[(CALL_R, 4)]),
        twin: "verus! {\nfn r() -> u64 { 1 }\nfn test() { let mut x: u64 = 0; proof {\n    let y = 1u64;\n    x = 1;\n} }\n}\n",
        twin_expect: rejected(&[(ASSIGN, 5)]),
    },
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
fn proof_blocks_and_their_twins() {
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
