// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the ESCAPING-CLOSURE body panic-freedom soundness suite
// (`closure_escape_body_soundness.rs`). Verified via verify_function_from_file,
// cache-OFF.
//
// Every closure below has a body that ALWAYS panics (`x / 0`), so a `Verified`
// verdict on any `_cx` function is a FALSE VERIFY. The `_ok` functions are the
// over-rejection controls: honest closure bodies that must keep verifying.

// A higher-order exec callee. Its body applies the closure it is handed.
fn g1_apply(g: impl Fn(u64) -> u64, a: u64) -> u64 {
    g(a)
}

fn g2_apply(g: impl Fn(u64, u64) -> u64, a: u64, b: u64) -> u64 {
    g(a, b)
}

struct Holder<F: Fn(u64) -> u64> {
    f: F,
}

// ---------------------------------------------------------------------------
// CONTROL (the currently-correct path): the closure is called DIRECTLY, so the
// call-site substitution instruments `x / 0` and COUNTEREXAMPLES.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e0_direct_call_cx(a: u64) {
    let g = |x: u64| x / 0u64;
    let _ = g(a);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E1 HIGHER-ORDER ARGUMENT: `g` escapes as an argument to `g1_apply`.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e1_higher_order_arg_cx(a: u64) {
    let g = |x: u64| x / 0u64;
    let _ = g1_apply(g, a);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E2 INLINE ARGUMENT LITERAL: the closure literal is written at the call site.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e2_inline_arg_literal_cx(a: u64) {
    let _ = g1_apply(|x: u64| x / 0u64, a);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E3 STRUCT FIELD: the closure is stored in a struct and never called here.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e3_struct_field_cx(a: u64) {
    let g = |x: u64| x / 0u64;
    let h = Holder { f: g };
    let _ = h;
    let _ = a;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E4 TUPLE: the closure is stored in a tuple.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e4_tuple_cx(a: u64) {
    let g = |x: u64| x / 0u64;
    let t = (g, a);
    let _ = t;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E5 RETURNED: the closure is the function's return value.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e5_returned_cx() -> impl Fn(u64) -> u64 {
    let g = |x: u64| x / 0u64;
    trust_vc::assert!(true);
    g
}

// ---------------------------------------------------------------------------
// E6 SHADOWED: the closure is bound, then the name is rebound to something
// harmless before any call. The unsafe body is never reachable from a call site.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e6_shadowed_cx(a: u64) {
    let g = |x: u64| x / 0u64;
    let g = |x: u64| x + 0u64;
    let _ = g(a);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E7 CAPTURED BY ANOTHER CLOSURE: `g` is only ever named inside a second
// closure, which is itself never called.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e7_captured_by_closure_cx(a: u64) {
    let g = |x: u64| x / 0u64;
    let outer = move |y: u64| g(y);
    let _ = outer;
    let _ = a;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E8 NEVER CALLED AT ALL: a bound closure with no use whatsoever.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e8_never_called_cx(a: u64) {
    let g = |x: u64| x / 0u64;
    let _ = a;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E9 ANONYMOUS, NEVER BOUND: a closure literal in statement position.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e9_statement_literal_cx(a: u64) {
    let _ = |x: u64| x / 0u64;
    let _ = a;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// H7 NEVER-CALLED `assume!(false)`: the contradictory hypothesis inside a
// never-called closure body must not discharge the parent's `assert!(false)`.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn h7_never_called_assume_false_cx(a: u64) {
    let g = |x: u64| {
        trust_vc::assume!(false);
        x
    };
    let _ = g;
    let _ = a;
    trust_vc::assert!(a != a);
}

// ---------------------------------------------------------------------------
// OVER-REJECTION CONTROLS — these must keep VERIFYING.
// ---------------------------------------------------------------------------

// A1 an honest escaping closure: body is total, so it must verify.
#[trust_vc::ensures(true)]
fn a1_honest_higher_order_arg_ok(a: u64) {
    let g = |x: u64| x / 2u64;
    let _ = g1_apply(g, a);
    trust_vc::assert!(true);
}

// A2 an honest inline literal argument.
#[trust_vc::ensures(true)]
fn a2_honest_inline_arg_ok(a: u64) {
    let _ = g1_apply(|x: u64| x / 2u64, a);
    trust_vc::assert!(true);
}

// A3 an honest never-called closure.
#[trust_vc::ensures(true)]
fn a3_honest_never_called_ok(a: u64) {
    let g = |x: u64| x / 2u64;
    let _ = g;
    let _ = a;
    trust_vc::assert!(true);
}

// A4 the EXISTING direct-call capability: a divisor that is only safe because of
// the CALL ARGUMENT must keep verifying (no definition-site over-rejection of a
// closure whose every use is a safe direct call).
#[trust_vc::ensures(true)]
fn a4_direct_call_safe_arg_ok(a: u64) {
    let g = |x: u64, y: u64| x / y;
    let _ = g(a, 5u64);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E10 FRESH-PARAMETER FRAME: an escaping closure's PARAMETERS are arbitrary —
// nothing at the definition site knows what a caller (or an escape target this
// function cannot see) will pass. The divisor is a parameter, so this must
// COUNTEREXAMPLE, not merely error out. Liar twin of A5.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e10_escaping_symbolic_divisor_cx(a: u64, b: u64) {
    let g = |x: u64, y: u64| x / y;
    let _ = g2_apply(g, a, b);
    trust_vc::assert!(true);
}

// A5 the honest twin of E10: same escape, same arity, a literal divisor.
#[trust_vc::ensures(true)]
fn a5_escaping_literal_divisor_ok(a: u64, b: u64) {
    let g = |x: u64, y: u64| x / 2u64;
    let _ = g2_apply(g, a, b);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E11 PATH CONDITION AT THE DEFINITION: the closure is defined on the branch
// where the captured divisor IS zero, so its body obligation must be discharged
// under that path condition and FAIL. Liar twin of A7.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e11_definition_path_condition_cx(a: u64, d: u64) {
    if d == 0u64 {
        let g = |x: u64| x / d;
        let _ = g1_apply(g, a);
    }
    trust_vc::assert!(true);
}

// A7 the honest twin of E11: the SAME closure defined on the branch where the
// capture is provably non-zero must still VERIFY — the definition-site path
// condition reaches the body obligation.
#[trust_vc::ensures(true)]
fn a7_definition_path_condition_ok(a: u64, d: u64) {
    if d != 0u64 {
        let g = |x: u64| x / d;
        let _ = g1_apply(g, a);
    }
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E12 FRAME, "no leak IN": the closure PARAMETER `x` shadows an enclosing
// parameter `x` that the function's `requires` says is non-zero. A closure body
// sees its captures and its parameters and nothing else, so the outer fact must
// NOT reach the closure's own `x`. A `Verified` here means a parent fact leaked
// into the closure frame. Liar twin of A8.
// ---------------------------------------------------------------------------
#[trust_vc::requires(x != 0u64)]
#[trust_vc::ensures(true)]
fn e12_outer_fact_must_not_reach_param_cx(a: u64, x: u64) {
    let g = |x: u64| a / x;
    let _ = g1_apply(g, a);
    trust_vc::assert!(true);
}

// A8 the honest twin of E12: a GENUINE capture's fact DOES reach the body, so
// the same division verifies when the non-zero name is captured, not shadowed.
#[trust_vc::requires(d != 0u64)]
#[trust_vc::ensures(true)]
fn a8_capture_fact_reaches_body_ok(a: u64, d: u64) {
    let g = |x: u64| a / d;
    let _ = g1_apply(g, a);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// A6 SPEC-CLOSURE control: a ghost closure handed to `Seq::new` has no runtime
// panic obligation and must never be instrumented, whether written inline or
// bound to a local first. Both must VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn a6_spec_closure_inline_ok(n: u64) {
    let s = trust_vc_types::Seq::new(n, |i| ((i + 1) as i32) * 10);
    let _ = s;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a6b_spec_closure_named_ok(n: u64) {
    let gen = |i: int| ((i + 1) as i32) * 10;
    let s = trust_vc_types::Seq::new(n, gen);
    let _ = s;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E13 INNER-BLOCK SHADOW: the name is re-bound inside a NESTED block, and the
// call there applies the INNER closure. Treating that call as coverage for the
// OUTER closure would leave the outer body checked nowhere.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e13_inner_block_shadow_cx(a: u64) {
    let g = |x: u64| x / 0u64;
    {
        let g = |x: u64| x + 0u64;
        let _ = g(a);
    }
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E14 CALLED ONLY INSIDE A LOOP: the call-site lane DEFERS inside a loop body,
// so a call there is not coverage either. Liar twin of A9.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e14_called_only_in_loop_cx(a: u64, n: u64) {
    let g = |x: u64| x / 0u64;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let _ = g(a);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// A9 the honest twin of E14: the identical loop shape with a total closure body
// must still VERIFY, so E14 is not vacuously failing on the loop.
#[trust_vc::ensures(true)]
fn a9_loop_called_honest_ok(a: u64, n: u64) {
    let g = |x: u64| x / 2u64;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let _ = g(a);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// H7b HONEST TWIN of H7: the closure's OWN `assume ⟹ assert` reasoning stays
// intact under the body scoping — both sides live inside the body window.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn h7b_closure_own_assume_implies_assert_ok(n: u64) {
    let g = |x: u64| {
        trust_vc::assume!(n > 100u64);
        trust_vc::assert!(n > 50u64);
        x
    };
    let _ = g;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// H7c the non-`false` sibling: a closure-body `assume!(n == 7)` must not
// discharge the ENCLOSING function's `assert!(n == 7)`.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn h7c_body_assume_does_not_reach_parent_cx(n: u64) {
    let g = |x: u64| {
        trust_vc::assume!(n == 7u64);
        x
    };
    let _ = g;
    trust_vc::assert!(n == 7u64);
}

// ---------------------------------------------------------------------------
// H7d ORDER: a LATER `assume!(false)` must not discharge an EARLIER in-body
// assertion. Guarding every body assertion with the whole window's assumptions
// would turn the leak-out fix into a leak-INWARDS false verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn h7d_later_assume_must_not_discharge_earlier_assert_cx(n: u64) {
    let g = |x: u64| {
        trust_vc::assert!(n == 7u64);
        trust_vc::assume!(false);
        x
    };
    let _ = g;
    let _ = n;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// H7e VACUITY DOES NOT ESCAPE. A contradictory in-body `assume!` makes the
// CLOSURE BODY's own downstream obligations vacuous — that is what `assume`
// means, and it is what Verus does — but the vacuity must stay INSIDE the body:
// the enclosing function's own FALSE goal must still be refuted. Before the body
// scoping, the `assume!(false)` was a parent hypothesis and the whole function
// went vacuous (`Unknown { VacuousTruth }`), which published nothing but also
// checked nothing.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn h7e_body_vacuity_does_not_escape_cx(a: u64, b: u64) {
    let g = |x: u64, y: u64| {
        trust_vc::assume!(false);
        x / y
    };
    let _ = g2_apply(g, a, b);
    trust_vc::assert!(a != a);
}

// H7f the honest twin of H7e: the SAME vacuous closure, and a TRUE parent goal
// — the parent must still verify, so H7e is refuted on its own merits and not
// because a vacuous closure poisons the enclosing function.
#[trust_vc::ensures(true)]
fn h7f_body_vacuity_leaves_parent_provable_ok(a: u64, b: u64) {
    let g = |x: u64, y: u64| {
        trust_vc::assume!(false);
        x / y
    };
    let _ = g2_apply(g, a, b);
    trust_vc::assert!(a == a);
}

// ===========================================================================
// ROUND-2 additions. Each closes a route the first increment left open, and
// each has an honest twin of the SAME shape.
// ===========================================================================

fn g1_apply_twice(mut g: impl FnMut(u64) -> u64, a: u64) -> u64 {
    let _ = g(a);
    g(a)
}

// ---------------------------------------------------------------------------
// E15 GHOST-SINK METHOD NAME on an EXEC receiver. `map`/`filter`/`fold` are
// `pure_ghost_collection_combinator` NAMES, and the modeled type cannot tell an
// immutable ghost `Seq` from an exec `Vec`, so keying the ghost skip on the name
// alone skipped every exec `.map`/`.filter`/`.fold` closure — the single most
// common way a real Rust closure escapes — and the body was checked nowhere.
// The divisor is a PARAMETER, so the panic is real and symbolic (not an encoder
// constant-fold artifact).
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e15_ghost_sink_method_inline_cx(v: Vec<u64>, b: u64) {
    let _ = v.iter().map(|x: u64| x / b);
    trust_vc::assert!(true);
}

// E16 the NAMED spelling of the same route, through the use-coverage scan
// rather than the planner's inline skip.
#[trust_vc::ensures(true)]
fn e16_ghost_sink_method_named_cx(v: Vec<u64>) {
    let g = |x: u64, y: u64| x / y;
    let _ = v.filter(g);
    trust_vc::assert!(true);
}

// A10 the honest twin of E15/E16: the identical combinator shape with a total
// body must keep verifying.
#[trust_vc::ensures(true)]
fn a10_ghost_sink_method_honest_ok(v: Vec<u64>) {
    let _ = v.iter().map(|x: u64| x / 2u64);
    trust_vc::assert!(true);
}

// A11 the CAPABILITY the name-only skip existed to protect: a genuine SPEC
// closure handed to a ghost combinator is written untyped (its parameter is a
// ghost index), is not instrumented, and still verifies.
#[trust_vc::ensures(true)]
fn a11_spec_closure_on_combinator_ok(n: u64) {
    let s = trust_vc_types::Seq::new(n, |i| ((i + 1) as i32) * 10);
    let t = s.map(|i| i);
    let _ = t;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E17 RE-ENTRANCY. A definition-site check that models ONE application starting
// from the capture's definition-site value checks only the FIRST call. This
// `FnMut` sets its own divisor to 0, so the SECOND application divides by zero
// unconditionally — the body must be checked over an ARBITRARY value of every
// capture the body itself writes.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e17_fnmut_second_application_cx(a: u64) {
    let mut d = 1u64;
    let g = move |x: u64| {
        let r = x / d;
        d = 0u64;
        r
    };
    let _ = g1_apply_twice(g, a);
    trust_vc::assert!(true);
}

// A12 the honest twin: a closure that mutates a capture but whose body is total
// on EVERY application must still verify — the freshening is confined to the
// captures the body writes, so this is not a blanket rejection of `FnMut`.
#[trust_vc::ensures(true)]
fn a12_mutating_capture_honest_ok(a: u64) {
    let mut c = 0u64;
    let g = move |x: u64| {
        c = 1u64;
        x / 2u64
    };
    let _ = g1_apply(g, a);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E18 INLINE LITERAL handed to a MODELED collection mutator. Every modeled
// mutator (`push`/`insert`/`remove`/…) returns before the generic argument walk,
// so a closure literal written inline as one of its arguments was never visited
// AT ALL — the planner's decision never even got to apply.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e18_inline_literal_pushed_cx() {
    let mut v = Vec::new();
    v.push(|x: u64, y: u64| x / y);
    trust_vc::assert!(true);
}

// A13 the honest twin of E18.
#[trust_vc::ensures(true)]
fn a13_inline_literal_pushed_honest_ok() {
    let mut v = Vec::new();
    v.push(|x: u64| x / 2u64);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E19 DEFINED INSIDE A LOOP. `e14` pins the neighbouring case (a closure CALLED
// inside a loop); this one is DEFINED there, and the definition-site emitter
// used to defer inside any loop context — so the body was checked at neither
// its definition nor its call. The loop-body arithmetic lane already renders
// over the loop-body havoc symbols and weakens by guard + invariant, so the
// definition-site obligation belongs there like any other body-site one.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e19_defined_inside_a_loop_cx(n: u64, a: u64, b: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let g = |x: u64, y: u64| x / y;
        let _ = g2_apply(g, a, b);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// A14 the honest twin of E19. LOAD-SENSITIVE for the same documented reason as
// `a9`: its goal is a loop invariant, and ay answers
// `(incomplete self-check-rejected)` on a busy box. Re-run ALONE before
// attributing a red here to the definition-site emitter.
#[trust_vc::ensures(true)]
fn a14_loop_defined_honest_ok(n: u64, a: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let g = |x: u64| x / 2u64;
        let _ = g1_apply(g, a);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// H7g DOMINANCE. An in-body `assume!` discharges the body's own downstream
// obligations (that is what `assume` means, and it is Verus's rule), but only
// the obligations it DOMINATES. Here the `assume!(false)` sits under `if x > 0`,
// so the division — which also runs when `x == 0` — must still be refuted. A
// `Verified` means the body's hypotheses were conjoined path-insensitively,
// which would make `assume!` an unconditional off switch for the whole body.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn h7g_branch_local_assume_does_not_discharge_cx(a: u64, b: u64) {
    let g = |x: u64, y: u64| {
        if x > 0u64 {
            trust_vc::assume!(false);
        }
        x / y
    };
    let _ = g2_apply(g, a, b);
    trust_vc::assert!(true);
}

// H7h a NESTED closure's `assume!(false)` is that closure's hypothesis, not the
// enclosing closure's: it must not discharge the OUTER body's division.
#[trust_vc::ensures(true)]
fn h7h_nested_closure_assume_does_not_discharge_cx(a: u64, b: u64) {
    let g = |x: u64, y: u64| {
        let z = |_w: u64| {
            trust_vc::assume!(false);
            0u64
        };
        let _ = z;
        x / y
    };
    let _ = g2_apply(g, a, b);
    trust_vc::assert!(true);
}

// A15 the honest twin of H7g/H7h and the retained `assume` CAPABILITY: an
// in-body `assume!` that genuinely establishes the divisor discharges the
// body's division, and the function verifies.
#[trust_vc::ensures(true)]
fn a15_body_assume_discharges_its_own_body_ok(a: u64, b: u64) {
    let g = |x: u64, y: u64| {
        trust_vc::assume!(y != 0u64);
        x / y
    };
    let _ = g2_apply(g, a, b);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// A16 the DEFINITION-SITE PATH CONDITION, symbolic. A closure defined in a
// provably-dead branch carries no obligation, so the function verifies. This is
// the twin that shows the path condition threaded into the definition-site
// check is real and not merely an accident of `e11`'s polarity.
//
// MEASURED RESIDUAL (pre-existing, engine-wide, NOT introduced here): the same
// shape with a LITERAL `0` divisor is an `Error`, because a constant-0 divisor
// is a hard ENCODE refusal before any path condition applies. Plain non-closure
// code has the identical behaviour — `if a != a { let _ = a / 0u64; }` is the
// same `Error` on this tree and at the merge base — so it is a property of the
// arithmetic encoder, not of the closure lane. Not pinned, because pinning it
// would cement the defect.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn a16_dead_branch_definition_ok(a: u64, d: u64) {
    if a != a {
        let g = |x: u64| x / d;
        let _ = g1_apply(g, a);
    }
    trust_vc::assert!(true);
}

// ===========================================================================
// ROUND 3 — a CONDITIONAL rebind is not a kill (the "adding a use disables the
// check" defect), the ghost-CONSTRUCTOR sink's exec-typed escape, and the
// definition-site frame's disclosed over-approximation.
// ===========================================================================

// ---------------------------------------------------------------------------
// E20 ONE-ARM REBIND THEN CALLED. `g` is rebound on ONE arm only, so the
// ORIGINAL `x / y` body still runs when `c` is false and `g(a, 0)` divides by
// zero. The use-coverage scan counted the one-arm write as a KILL and the later
// `g(a, 0)` as coverage, so the DEFINITION site emitted nothing; meanwhile
// `reapply_common_branch_exec_closure_rebinds` had already cleared
// `exec_closure_defs["g"]` (it only reinstates a body BOTH arms agree on), so
// the CALL site emitted nothing either. Checked at neither site.
//
// E20B IS THE DECISIVE PAIR: the identical function with the call DELETED
// counterexamples. Adding a direct call made an unchecked closure LESS checked
// — a check that can be disabled by adding a use is not a check.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e20_one_arm_rebind_then_called_cx(a: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    if c {
        g = |x: u64, _y: u64| x / 2u64;
    }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e20b_one_arm_rebind_not_called_cx(a: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    if c {
        g = |x: u64, _y: u64| x / 2u64;
    }
    trust_vc::assert!(true);
}

// E21 the `else`-only spelling of the same route.
#[trust_vc::ensures(true)]
fn e21_else_only_rebind_then_called_cx(a: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    if c {
    } else {
        g = |x: u64, _y: u64| x / 2u64;
    }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// E22 a MATCH arm is conditional too.
#[trust_vc::ensures(true)]
fn e22_match_arm_rebind_then_called_cx(a: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    match c {
        true => {
            g = |x: u64, _y: u64| x / 2u64;
        }
        false => {}
    }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// E23 a LOOP body may iterate zero times, so a rebind inside it is conditional.
#[trust_vc::ensures(true)]
fn e23_loop_rebind_then_called_cx(a: u64, n: u64) {
    let mut g = |x: u64, y: u64| x / y;
    let mut i = 0u64;
    while i < n {
        g = |x: u64, _y: u64| x / 2u64;
        i = i + 1u64;
    }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// A17 the over-rejection twin of E20: the SAME one-arm rebind shape with both
// bodies total. It is true, but it is refused: the join leaves `g` unmodelled,
// and an application of an unmodelled function value fails closed at
// extraction because its requires cannot be proven at the call.
#[trust_vc::ensures(true)]
fn a17_one_arm_rebind_honest_ok(a: u64, c: bool) {
    let mut g = |x: u64, _y: u64| x / 3u64;
    if c {
        g = |x: u64, _y: u64| x / 2u64;
    }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// A18 THE RECOVERED CAPABILITY. A straight-line UNCONDITIONAL rebind kills the
// first literal outright — its body can never run, so it carries no obligation
// and the only live body (`x / 2`) is safe at `g(a, 0)`. This was an `Error`
// before round 3 (the first increment demanded a classified USE before it would
// believe a rebind), a measured over-rejection against the merge base, and it
// is now the direct dual of E20: unconditional kills are believed, conditional
// ones are not.
#[trust_vc::ensures(true)]
fn a18_unconditional_straightline_rebind_ok(a: u64) {
    let mut g = |x: u64, y: u64| x / y;
    g = |x: u64, _y: u64| x / 2u64;
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// A19 both arms rebind, to DIFFERENT (total) bodies: still an unconditional
// kill of the original, and each new literal is checked at its own definition.
// `reapply_common_branch_exec_closure_rebinds` reinstates nothing here (the
// bodies differ), so `g` is unmodelled after the join and its application is
// refused, as for A17.
#[trust_vc::ensures(true)]
fn a19_both_arms_differing_safe_rebind_ok(a: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    if c {
        g = |x: u64, _y: u64| x / 2u64;
    } else {
        g = |x: u64, _y: u64| x / 3u64;
    }
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// E24/E25 RETIRED IN ROUND 6, with their bodies KEPT: the identical two
// functions now live as `a40_ghost_ctor_exec_param_is_spec_ok` and
// `a41_ghost_ctor_exec_param_named_is_spec_ok` below, pinned to the opposite
// verdict. Round 3 read an exec-SPELLED closure parameter at a ghost constructor
// as "this is an exec closure"; the corpus's own `SpecFn::new(|i: usize| ...)`
// spec surface writes exactly that spelling, and the override turned two GREEN
// lib tests red. A ghost constructor builds a SPEC value: its closure argument
// is a spec function whose body never executes. The protective content of the
// override — a closure that ALSO escapes or is called — is `e24c`/`e24d`.

// A20 the over-rejection twin of the ghost-constructor rule: an exec-typed closure at a ghost
// constructor whose body IS total keeps verifying. Together with A6/A6B (the
// untyped and `int`-typed spec spellings, which stay uninstrumented) this is
// the whole constructor rule.
#[trust_vc::ensures(true)]
fn a20_ghost_ctor_exec_param_honest_ok(n: u64) {
    let _ = trust_vc_types::Seq::new(n, |i: u64| 10u64 / 2u64);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// X1 A DISCLOSED CAPABILITY REGRESSION, pinned as intended rather than left
// undisclosed. A definition-site check ranges over an ARBITRARY parameter value
// (E10/E12 pin that the frame must know nothing about it), so unguarded
// arithmetic on the parameter — `x + 1` — is genuinely refutable and this
// function, which `Verified` at the merge base only because nothing checked the
// body at all, is now rejected. It is NOT narrowable: any fact that would
// discharge it is a fact the frame must not have. Measured for `+` and `*`,
// and for the ghost-constructor sink (`Seq::new(n, |i: u64| i + 1u64)`) since
// E24 brought that sink under the same rule.
//
// A21 IS THE REMEDY, and the reason this is an over-approximation rather than a
// wall: guard the arithmetic in the body and the identical shape verifies.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn x1_unguarded_param_arith_is_rejected_cx(v: Vec<u64>) {
    let _ = v.map(|x: u64| x + 1u64);
    trust_vc::assert!(true);
}

// A46 (round 6) - WAS `x1b`, the ghost-CONSTRUCTOR instance of the X1 class,
// and it is the THIRD over-rejection round 3's constructor override caused
// (the other two are the `seq_concrete_ext_eq` lib fixtures). The receiver is a
// SPEC constructor, so `i + 1u64` is spec arithmetic in a body that never runs -
// it verified at the MERGE BASE and it verifies again. X1/X1C keep the pin for
// the genuine EXEC receiver, where the over-approximation is real.
#[trust_vc::ensures(true)]
fn a46_ghost_ctor_param_arith_ok(n: u64) {
    let _ = trust_vc_types::Seq::new(n, |i: u64| i + 1u64);
    trust_vc::assert!(true);
}

// X1C SUBTRACTION is the fourth instance of the same class, named here because
// round 3's disclosure listed only `+`, `*` and the ghost-constructor `+`.
#[trust_vc::ensures(true)]
fn x1c_unguarded_param_sub_is_rejected_cx(v: Vec<u64>) {
    let _ = v.map(|x: u64| x - 1u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a21_guarded_param_arith_ok(v: Vec<u64>) {
    let _ = v.map(|x: u64| if x < 100u64 { x + 1u64 } else { 0u64 });
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// W1 MACRO OPACITY, measured and disclosed as ENGINE-WIDE and PRE-EXISTING, not
// a closure defect. A closure literal written inside an opaque macro token
// stream (`vec![|x: u64, y: u64| x / y]`) is invisible to the planner and to the
// collector, so it keeps the pre-fix behaviour. W1B IS THE CONTROL that settles
// the attribution: PLAIN arithmetic inside the same macro
// (`vec![10u64 / 0u64]`) is equally invisible and equally `Verified`, at the
// merge base and here. W2 shows the boundary is the LITERAL, not the name: the
// named spelling IS caught, because the use-coverage scan treats an ident inside
// a macro token stream as an unclassified use.
//
// W1/W1B are NOT pinned: asserting their current verdict would cement a
// false-`Verified`. W2 is pinned, because it asserts the closed half.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn w2_macro_named_closure_cx(a: u64) {
    let g = |x: u64, y: u64| x / y;
    let v = vec![g];
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// E26 THE SIBLING ARM. Round 3's "an unconditional kill ends the scan" rule has
// one way to be wrong: inside an `if`/`else` whose arms BOTH write the name, the
// arms are ALTERNATIVE paths, not successive ones. Stopping at the FIRST arm's
// write hides everything the OTHER arm does with the still-live original — here
// an escape into `g2_apply`, which reaches no call site at all. Measured
// false-`Verified` with the stop in place, and the arm ORDER is what makes it
// reachable: the bare-kill arm must come first.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e26_sibling_arm_escape_after_a_both_arms_kill_cx(a: u64, b: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    if c {
        g = |x: u64, _y: u64| x / 2u64;
    } else {
        let _ = g2_apply(g, a, b);
        g = |x: u64, _y: u64| x / 2u64;
    }
    trust_vc::assert!(true);
}

// A22 the over-rejection twin: the same sibling-arm shape with a total original
// body. The kill is still believed (the join is still a kill), the sibling arm
// is still scanned, and the definition-site check on the original passes.
#[trust_vc::ensures(true)]
fn a22_sibling_arm_escape_after_a_both_arms_kill_ok(a: u64, b: u64, c: bool) {
    let mut g = |x: u64, _y: u64| x / 2u64;
    if c {
        g = |x: u64, _y: u64| x / 3u64;
    } else {
        let _ = g2_apply(g, a, b);
        g = |x: u64, _y: u64| x / 3u64;
    }
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// ROUND 4 — THE IN-LOOP DEFINE-AND-CALL. `e14` pins a closure defined OUTSIDE a
// loop and called inside it; `e19` pins one DEFINED inside a loop that ESCAPES.
// This is the third corner, and it was checked at NEITHER site: the use-coverage
// scan is block-local, so a binding in a loop-body block started its walk with
// no evidence of the enclosing loop and classified the in-loop `g(a, 0)` as a
// COVERING call — while `maybe_emit_invoked_exec_closure_arith_safety` bails
// outright inside any loop context. `e27b` is the decisive pair: the identical
// function with the CALL DELETED counterexamples, so ADDING A USE made an
// unchecked closure LESS checked. A check that can be disabled by adding a use
// is not a check.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e27_defined_and_called_inside_a_loop_cx(a: u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let g = |x: u64, y: u64| x / y;
        let _ = g(a, 0u64);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// E27B THE DECISIVE PAIR of E27: the same function with the call line DELETED.
// It counterexampled before this fix as well — that asymmetry IS the defect.
#[trust_vc::ensures(true)]
fn e27b_defined_inside_a_loop_never_called_cx(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let g = |x: u64, y: u64| x / y;
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// E27C the SYMBOLIC-argument spelling: the divisor is a parameter, so the
// counterexample cannot come from folding a literal zero at the call.
#[trust_vc::ensures(true)]
fn e27c_defined_and_called_inside_a_loop_symbolic_cx(a: u64, b: u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let g = |x: u64, y: u64| x / y;
        let _ = g(a, b);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// A23 the honest twin of E27/E27C: the identical shape with a total body must
// keep verifying, so neither pin is passing on the loop alone.
#[trust_vc::ensures(true)]
fn a23_defined_and_called_inside_a_loop_honest_ok(a: u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let g = |x: u64, _y: u64| x / 2u64;
        let _ = g(a, 0u64);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// E28 THE IMMEDIATELY-INVOKED LITERAL, same hole, other spelling. The planner
// skipped `(|x, y| x / y)(a, b)` on the grounds that the call-site lane
// instruments it with the actual arguments — true at the top level, false inside
// a loop, where that lane bails.
#[trust_vc::ensures(true)]
fn e28_immediately_invoked_literal_inside_a_loop_cx(a: u64, b: u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let _ = (|x: u64, y: u64| x / y)(a, b);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// A23B the honest twin of E28.
#[trust_vc::ensures(true)]
fn a23b_immediately_invoked_literal_inside_a_loop_honest_ok(a: u64, n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let _ = (|x: u64, _y: u64| x / 2u64)(a, 0u64);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// E29 the `for` spelling of E27: the loop depth must be carried by every loop
// form, not just `while`.
#[trust_vc::ensures(true)]
fn e29_defined_and_called_inside_a_for_loop_cx(a: u64, n: u64) {
    let mut s = 0u64;
    for _k in 0u64..n {
        let g = |x: u64, y: u64| x / y;
        s = g(a, 0u64);
    }
    trust_vc::assert!(true);
}

// A25 the honest twin of E29.
#[trust_vc::ensures(true)]
fn a25_defined_and_called_inside_a_for_loop_honest_ok(a: u64, n: u64) {
    let mut s = 0u64;
    for _k in 0u64..n {
        let g = |x: u64, _y: u64| x / 2u64;
        s = g(a, 0u64);
    }
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// ROUND 4 — THE OVER-REJECTION ROUND 3b OPENED. The sibling-arm suppression
// (`e26`) correctly keeps the scan walking past the FIRST arm's write so the
// OTHER arm is still scanned — but it also kept attributing uses that come
// after an arm's OWN write to the original literal, which is dead from that
// point ON THAT PATH. A24 verified at the merge base and was rejected here: both
// live bodies divide by a nonzero constant, so this is not the disclosed `x1`
// class. The kill is now ARM-LOCAL.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn a24_escape_after_an_in_arm_write_ok(a: u64, b: u64, c: bool) {
    let mut g = |x: u64, y: u64| x / y;
    if c {
        g = |x: u64, _y: u64| x / 2u64;
        let _ = g2_apply(g, a, b);
    } else {
        g = |x: u64, _y: u64| x / 3u64;
    }
    trust_vc::assert!(true);
}

// E30 the liar twin of A24, and the proof that the arm-local kill only MOVES the
// obligation to the literal that actually escapes rather than deleting it: the
// original is safe, the literal written by the arm is not, and it escapes.
#[trust_vc::ensures(true)]
fn e30_escape_after_an_in_arm_write_of_an_unsafe_literal_cx(a: u64, b: u64, c: bool) {
    let mut g = |x: u64, _y: u64| x / 2u64;
    if c {
        g = |x: u64, y: u64| x / y;
        let _ = g2_apply(g, a, b);
    } else {
        g = |x: u64, _y: u64| x / 3u64;
    }
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// ROUND 4 — THE CALL-SITE-UNINSTRUMENTABLE GUARD, which round 3 shipped with no
// named discriminator. `closure_uses_are_covered` opens with
// `closure_is_call_site_instrumentable`, mirroring the two bails in
// `maybe_emit_invoked_exec_closure_arith_safety` (a non-simple-ident parameter,
// and a body that re-binds a parameter name). Without it a DIRECT CALL on such a
// closure counts as coverage while the lane it defers to bails, so the body is
// checked at neither site. E31 is that shape and A26 is its honest twin.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn e31_body_rebinds_a_param_then_called_cx(a: u64, b: u64) {
    let g = |x: u64, y: u64| {
        let y = b;
        x / y
    };
    let _ = g(a, 1u64);
    trust_vc::assert!(true);
}

// A26: the body re-binds the parameter to a SAFE divisor, so the call passing
// `0` is irrelevant and the definition-site check passes.
#[trust_vc::ensures(true)]
fn a26_body_rebinds_a_param_honest_ok(a: u64) {
    let g = |x: u64, y: u64| {
        let y = 2u64;
        x / y
    };
    let _ = g(a, 0u64);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// ROUND 4 — THE RESIDUALS BECOME EXECUTABLE. Round 3 disclosed both residuals in
// PROSE only, so nothing in the tree would surface a change in their status —
// neither a fix that closes them nor a regression that widens them. Their
// verdict is still deliberately NOT pinned (asserting `Verified` would cement a
// false-verify). What IS pinned is that each residual is INDISCRIMINATE: the
// liar and its honest structural twin get the SAME verdict, because the skip
// looks at neither. The day a residual closes, the two diverge and the pin
// fires — which is the signal to re-key it, not to silence it.
//
// ROUTE A, and TWO SPELLINGS ROUND 3's HEADER DID NOT NAME:
//   * U1/U1B  — an UNTYPED exec `.map` parameter keeps the ghost skip.
//   * U1C/U1D — a PARTIALLY annotated parameter list keeps it too
//     (`closure_params_are_written_exec_scalars` requires EVERY parameter), and
//   * U1E/U1F — round 3's own constructor-sink fix inherited the same predicate,
//     so the untyped residual now exists at the GHOST CONSTRUCTOR as well.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn u1_untyped_combinator_divzero_cx(v: Vec<u64>) {
    let _ = v.map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn u1b_untyped_combinator_honest_control(v: Vec<u64>) {
    let _ = v.map(|x| x / 2u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn u1c_partially_annotated_divzero_cx(v: Vec<u64>) {
    let _ = v.fold(0u64, |acc: u64, x| acc / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn u1d_partially_annotated_honest_control(v: Vec<u64>) {
    let _ = v.fold(0u64, |acc: u64, x| acc / 2u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn u1e_untyped_ghost_ctor_divzero_residual(n: u64) {
    let _ = trust_vc_types::Seq::new(n, |i| 10u64 / i);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn u1f_untyped_ghost_ctor_honest_control(n: u64) {
    let _ = trust_vc_types::Seq::new(n, |i| 10u64 / 2u64);
    trust_vc::assert!(true);
}

// ROUTE C, a closure literal inside `vec![..]`. The element is stored, never
// called here, so its body is checked at its definition like any escaping
// literal: W1 is refuted at `y = 0` and W1C, the guarded twin, verifies. W1B
// and W1D are plain arithmetic in the same macro: W1D is refuted like W1, and
// W1B's constant zero divisor is refused by the encoder, as it is outside a
// macro.
#[trust_vc::ensures(true)]
fn w1_macro_closure_literal_residual(a: u64) {
    let v = vec![|x: u64, y: u64| x / y];
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w1b_macro_plain_arith_control(a: u64) {
    let v = vec![10u64 / 0u64];
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w1c_macro_closure_literal_guarded_ok(a: u64) {
    let v = vec![|x: u64, y: u64| if y == 0u64 { 0u64 } else { x / y }];
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w1d_macro_plain_arith_param_control(a: u64) {
    let v = vec![10u64 / a];
    trust_vc::assert!(true);
}

// The repeat form and a nested `vec!`: the same literal, reached through the
// repeated element and through an inner macro's element.
#[trust_vc::ensures(true)]
fn w1e_macro_repeat_closure_literal_cx(a: u64) {
    let v = vec![|x: u64, y: u64| x / y; 3];
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w1f_macro_nested_closure_literal_cx(a: u64) {
    let v = vec![vec![|x: u64, y: u64| x / y]];
    trust_vc::assert!(true);
}

// An element's planner uses the enclosing loop depth: inside a loop the
// call-site lane does not instrument an invoked literal, so W1G is checked at
// its definition. W1H, the same call outside a loop with a safe argument, is
// covered by the call-site lane and verifies.
#[trust_vc::requires(n == 1u64)]
#[trust_vc::ensures(true)]
fn w1g_macro_invoked_literal_in_loop_cx(a: u64, b: u64, n: u64) {
    let mut i: u64 = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let _v = vec![(|x: u64, y: u64| x / y)(a, b)];
        i = i + 1u64;
    }
}

#[trust_vc::ensures(true)]
fn w1h_macro_invoked_literal_safe_ok(a: u64) {
    let _v = vec![(|x: u64, y: u64| x / y)(a, 1u64)];
}

// An element's planner classifies receivers with the function's `let`s: the
// destructuring `let` rebinds `v` to the exec `w`, so the literal is checked,
// not skipped as a spec closure over the ghost parameter `v`. W1J, over the
// ghost parameter itself, is a spec closure and verifies.
#[trust_vc::ensures(true)]
fn w1i_macro_shadowed_ghost_receiver_cx(v: Seq<u64>, w: Vec<u64>, a: u64) {
    let (v, _z) = (w, 0u64);
    let _x = vec![v.map(|_x| 10u64 / a)];
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn w1j_macro_ghost_receiver_spec_closure_ok(v: Seq<u64>, a: u64) {
    let _x = vec![v.map(|_x| 10u64 / a)];
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// ROUND 4 OVER-REJECTION CONTROLS for the planner's new depth carrying. Seeding
// the use scan with the enclosing depths makes MORE literals reach a
// definition-site check; these two are the shapes where that could have cost a
// capability, and both must keep verifying.
// ---------------------------------------------------------------------------

// A27: a SPEC closure bound inside a loop body and handed to a ghost sink there.
// The scan can no longer classify the ghost argument (a ghost use at depth > 0
// is unclassified, as it already was for a binding OUTSIDE the loop), so the
// literal reaches the definition-site check — which must find no runtime
// obligation in a ghost body.
#[trust_vc::ensures(true)]
fn a27_spec_closure_bound_inside_a_loop_ok(n: u64) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let gen = |i: int| ((i + 1) as i32) * 10;
        let s = trust_vc_types::Seq::new(n, gen);
        let _ = s;
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

// A28: a closure defined and called INSIDE another closure's body. The planner
// now carries closure depth too, so the inner literal is no longer skipped on
// the strength of a call the call-site lane may never reach.
#[trust_vc::ensures(true)]
fn a28_inner_closure_defined_and_called_in_an_outer_closure_ok(a: u64) {
    let outer = |z: u64| {
        let h = |x: u64, _y: u64| x / 2u64;
        h(z, 0u64)
    };
    let _ = g1_apply(outer, a);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// ROUND 5 - THE GHOST-SINK SKIP READS THE RECEIVER, NOT THE PARAMETER LIST.
//
// Route A was a live ADDING-A-USE-DISABLES-THE-CHECK route on THIS branch, not
// only at the merge base: the definition-site lane checks an escaping closure's
// body, and handing that same literal to `.map`/`.filter`/`.fold` switched the
// check back OFF whenever its parameter list was not FULLY written in exec
// scalar types. The skip now requires the RECEIVER to resolve as a ghost/spec
// collection; an EXEC receiver is checked with its element sort minted for the
// unwritten parameters, and an UNRESOLVED receiver is checked too (fail closed).
// ---------------------------------------------------------------------------

// N1 THE NAMED spelling of `u1`: the literal is written at its binding, so the
// receiver is reached through the use scan rather than through the planner's
// inline path. Pinned as a COUNTEREXAMPLE, not merely a non-verify: the
// parameter sort is inferred from the receiver's elements, so the body's
// obligation LOWERS and is refuted with a model.
#[trust_vc::ensures(true)]
fn n1_named_untyped_exec_map_cx(v: Vec<u64>) {
    let g = |x| 10u64 / x;
    let _ = v.map(g);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n1b_named_untyped_exec_map_ok(v: Vec<u64>) {
    let g = |x| x / 2u64;
    let _ = v.map(g);
    trust_vc::assert!(true);
}

// N2 the INLINE spelling of the same, and the pin that discriminates the
// parameter-sort INFERENCE on its own: without it this is an `unresolved
// variable` incompleteness rather than a refutation.
#[trust_vc::ensures(true)]
fn n2_untyped_exec_map_div_by_param_cx(v: Vec<u64>) {
    let _ = v.map(|x| 10u64 / x);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n2b_untyped_exec_map_guarded_param_ok(v: Vec<u64>) {
    let _ = v.map(|x| if x > 0u64 { 10u64 / x } else { 0u64 });
    trust_vc::assert!(true);
}

// N3 a `let`-ANNOTATED local receiver: the `VerificationContext` carries only
// function PARAMETERS before the body walk, so a local's Vec-vs-Seq provenance
// is read from its written annotation.
#[trust_vc::ensures(true)]
fn n3_local_vec_annotation_untyped_cx(a: u64) {
    let v: Vec<u64> = Vec::new();
    let _ = v.map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n3b_local_vec_annotation_untyped_ok(a: u64) {
    let v: Vec<u64> = Vec::new();
    let _ = v.map(|x| x / 2u64);
    trust_vc::assert!(true);
}

// N4 an ARRAY receiver and N5 a SLICE receiver: both are `bounded_len` exec
// collections and neither is a `Vec`.
#[trust_vc::ensures(true)]
fn n4_array_param_untyped_cx(ar: [u64; 4]) {
    let _ = ar.map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n4b_array_param_untyped_ok(ar: [u64; 4]) {
    let _ = ar.map(|x| x / 2u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n5_slice_param_untyped_cx(v: &[u64]) {
    let _ = v.map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n5b_slice_param_untyped_ok(v: &[u64]) {
    let _ = v.map(|x| x / 2u64);
    trust_vc::assert!(true);
}

// N6 a FOLD whose accumulator is untyped too: the accumulator's sort comes from
// the INITIAL VALUE, never from the receiver's elements.
#[trust_vc::ensures(true)]
fn n6_untyped_exec_fold_both_cx(v: Vec<u64>) {
    let _ = v.fold(0u64, |acc, x| acc / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n6b_untyped_exec_fold_both_ok(v: Vec<u64>) {
    let _ = v.fold(0u64, |acc, x| acc / 2u64);
    trust_vc::assert!(true);
}

// N7 AN UNRESOLVED RECEIVER FAILS CLOSED (requirement 3). An `if`/`else`
// receiver expression is not resolvable, and a wrong guess there is exactly the
// dangerous one, so the body is CHECKED. The measured fail-closed outcome is an
// `unresolved variable` incompleteness (the parameter has no sort to mint), i.e.
// a sound non-verify, never a `Verified`.
#[trust_vc::ensures(true)]
fn n7_unresolved_receiver_untyped_cx(v: Vec<u64>, c: bool) {
    let _ = (if c { v } else { v }).map(|x| x / 0u64);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// ROUND-5 DECISIVE-PAIR TWINS. Each is the identical closure body with the SINK
// DELETED. The bar: the verdict WITH the sink may never be a `Verified` where
// the verdict WITHOUT it is not - adding a use may not remove an obligation.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d1_u1_no_sink_twin(v: Vec<u64>) {
    let _g = |x| x / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d2_u1c_no_sink_twin(v: Vec<u64>) {
    let _g = |acc: u64, x| acc / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d3_n1_no_sink_twin(v: Vec<u64>) {
    let _g = |x| 10u64 / x;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d4_n6_no_sink_twin(v: Vec<u64>) {
    let _g = |acc, x| acc / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d5_u1e_no_sink_twin(n: u64) {
    let _g = |i| 10u64 / i;
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// ROUND-5 GHOST-SURFACE CONTROLS. Requirement 2: `Seq::new(..)`, `.map`,
// `.filter` and `.fold` over GENUINE spec collections must still verify -
// including UNTYPED spec closures and quantifier bodies containing arithmetic.
// Every one of these is a receiver the classifier must resolve as ghost.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn a29_ghost_seq_param_map_untyped_ok(s: Seq<int>) {
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a30_ghost_seq_param_filter_untyped_ok(s: Seq<int>) {
    let _ = s.filter(|i| i * 2 > 4);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a31_ghost_seq_param_fold_untyped_ok(s: Seq<int>) {
    let _ = s.fold(0, |acc, x| acc + x);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a32_ghost_ctor_chained_combinator_untyped_ok(n: u64) {
    let _ = trust_vc_types::Seq::new(n, |i| ((i + 1) as i32) * 10).map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a33_ghost_set_map_untyped_ok(s: Set<int>) {
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a34_ghost_map_values_untyped_ok(m: Map<int, int>) {
    let _ = m.map_values(|v| v + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a35_local_ghost_seq_annotation_untyped_ok(a: u64) {
    let s: Seq<int> = trust_vc_types::Seq::empty();
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a36_spec_quantifier_body_arith_ok(s: Seq<int>) {
    trust_vc::assert!(forall|k: int| 0 <= k && k < s.len() ==> s[k] + 1 > s[k]);
}

#[trust_vc::ensures(true)]
fn a37_named_untyped_ghost_seq_ok(s: Seq<int>) {
    let g = |i| i + 1;
    let _ = s.map(g);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a38_named_untyped_ghost_seq_fold_ok(s: Seq<int>) {
    let g = |acc, x| acc + x;
    let _ = s.fold(0, g);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a39_ghost_view_untyped_ok(v: Vec<u64>) {
    let _ = v.view().map(|x| x + 1);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// X2 A SECOND DISCLOSED CAPABILITY REGRESSION, pinned rather than hidden. Fail
// CLOSED on an unresolvable receiver costs the HONEST twin too: an untyped
// closure at a receiver the classifier cannot resolve has no sort to mint, so
// even a total body comes back an `unresolved variable` incompleteness. A45 is
// the NARROWING control - the identical honest body at a RESOLVED exec receiver
// still verifies - so the cost is exactly the unresolvable receiver and nothing
// wider.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn a45_branch_receiver_honest_ok(v: Vec<u64>, c: bool) {
    let _ = (if c { v } else { v }).map(|x| x / 2u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn x2b_chained_exec_receiver_honest_is_rejected(v: Vec<u64>) {
    let _ = v.map(|x: u64| x).map(|x| x / 2u64);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// U1K/U1L THE REMAINING ROUTE-A RESIDUAL, in its third spelling: a GHOST VIEW.
// `v@` (desugared `.view()`) of an exec `Vec` is a spec `Seq`, so a closure over
// it is a spec function and keeps the skip - the same reading that keeps `u1e`
// open at the ghost CONSTRUCTOR. Kept as an AGREEMENT pin, not a verdict pin.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn u1k_ghost_view_divzero_residual(v: Vec<u64>) {
    let _ = v.view().map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn u1l_ghost_view_honest_control(v: Vec<u64>) {
    let _ = v.view().map(|x| x / 2u64);
    trust_vc::assert!(true);
}

// N8 THE FOLD ACCUMULATOR'S SORT COMES FROM THE INITIAL VALUE, not from the
// receiver's elements. A `Vec<u64>` folded from a `0u32` seed has a `u32`
// accumulator, and minting it at the ELEMENT sort reports a `u64` model for a
// `u32` program variable — a counterexample that misdescribes the program.
#[trust_vc::ensures(true)]
fn n8_fold_accumulator_sort_from_init_cx(v: Vec<u64>) {
    let _ = v.fold(0u32, |acc, x| 10u32 / acc);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n8b_fold_accumulator_sort_from_init_ok(v: Vec<u64>) {
    let _ = v.fold(0u32, |acc, x| acc / 2u32);
    trust_vc::assert!(true);
}

// N9 A GHOST SHADOW MUST NOT RE-CLASSIFY AN EARLIER EXEC USE. The receiver
// environment's `let` map is FLAT over the whole body, so a later binding that
// SHADOWS a function parameter would otherwise decide uses that PRECEDE it - and
// a ghost shadow of an exec `Vec` would hand the earlier `.map` a skip it must
// not have. When the two readings disagree the classifier fails closed.
#[trust_vc::ensures(true)]
fn n9_ghost_shadow_does_not_reclassify_earlier_exec_use_cx(v: Vec<u64>, n: u64) {
    let _ = v.map(|x| x / 0u64);
    let v = trust_vc_types::Seq::new(n, |i| ((i + 1) as i32) * 10);
    let _ = v;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn n9b_ghost_shadow_honest_twin_ok(v: Vec<u64>, n: u64) {
    let _ = v.map(|x: u64| x / 2u64);
    let v = trust_vc_types::Seq::new(n, |i| ((i + 1) as i32) * 10);
    let _ = v;
    trust_vc::assert!(true);
}

// ===========================================================================
// ROUND 6. Three families, one rule: the ghost/spec skip is granted only on
// POSITIVE evidence that the receiver is a spec collection. Absence of exec
// evidence is not evidence.
// ===========================================================================

// ---------------------------------------------------------------------------
// P1-P6 AN EXEC STD SET/MAP IS NOT A GHOST COLLECTION. `BTreeSet<u64>` and
// `HashSet<u64>` model as `TrustVcType::Set`, `BTreeMap`/`HashMap` as `Map` -
// the SAME sorts the spec `Set`/`Map` use - and round 5 read "models as Set/Map"
// as ghost, so adding `.map` to an exec set removed the obligation. The origin
// SPELLING separates them, exactly as it separates `Vec` from `Seq`.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn p1_btreeset_map_untyped_cx(v: BTreeSet<u64>) {
    let _ = v.map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p1b_btreeset_map_untyped_ok(v: BTreeSet<u64>) {
    let _ = v.map(|x| x / 2u64);
    trust_vc::assert!(true);
}

// THE STRONGEST FORM: this obligation needs no parameter sort at all, so a
// non-verify here cannot be an inference gap - it is the skip itself.
// The MINT discriminator: the divisor is the PARAMETER, so this can only come
// back a COUNTEREXAMPLE if the receiver's element sort reached the definition
// site. Without the mint it is merely an `unresolved variable` incompleteness.
#[trust_vc::ensures(true)]
fn p1c_btreeset_div_by_param_cx(v: BTreeSet<u64>) {
    let _ = v.map(|x| 10u64 / x);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p2_btreeset_no_param_sort_cx(v: BTreeSet<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d6_p2_no_sink_twin(v: BTreeSet<u64>) {
    let _g = |_x| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p3_hashset_map_untyped_cx(v: HashSet<u64>) {
    let _ = v.map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p3b_hashset_map_untyped_ok(v: HashSet<u64>) {
    let _ = v.map(|x| x / 2u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p4_btreemap_map_values_cx(m: BTreeMap<u64, u64>) {
    let _ = m.map_values(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p4b_btreemap_map_values_ok(m: BTreeMap<u64, u64>) {
    let _ = m.map_values(|x| x / 2u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p5_hashmap_map_values_cx(m: HashMap<u64, u64>) {
    let _ = m.map_values(|x| x / 0u64);
    trust_vc::assert!(true);
}

// A `let` ANNOTATION already held the spelling and round 5 discarded it.
#[trust_vc::ensures(true)]
fn p6_let_annotated_btreeset_cx(v: BTreeSet<u64>) {
    let w: BTreeSet<u64> = v;
    let _ = w.map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p6b_let_annotated_btreeset_ok(v: BTreeSet<u64>) {
    let w: BTreeSet<u64> = v;
    let _ = w.map(|x| x / 2u64);
    trust_vc::assert!(true);
}

// An UNANNOTATED `let` initialised by an exec std constructor: the initializer
// is a call the classifier does not recognise, so it fails CLOSED (checked)
// rather than inheriting a ghost reading from the modeled `Set` sort.
#[trust_vc::ensures(true)]
fn p6c_unannotated_btreeset_local_cx() {
    let w = BTreeSet::new();
    let _ = w.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// THE NARROWING CONTROLS: the SPEC `Set`/`Map` spelling keeps the skip, so
// closing the exec side costs no spec surface.
#[trust_vc::ensures(true)]
fn a43_spec_set_divzero_still_skipped(s: Set<int>) {
    let _ = s.map(|i| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a44_spec_map_values_untyped_ok(m: Map<int, int>) {
    let _ = m.map_values(|v| v * 2);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// A40-A42 THE GHOST CONSTRUCTOR IS A GHOST RECEIVER, whatever its closure's
// parameters are spelled. Round 3 read an exec-scalar parameter type as "this
// is an exec closure" and checked the body; the corpus's own cardinal spec
// surface (`SpecFn::new(|i: usize| 10i32 * (i as i32))`, the lib fixtures
// `seq_concrete_ext_eq::*`) writes exactly that spelling and went RED.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn a40_ghost_ctor_exec_param_is_spec_ok(n: u64) {
    let _ = trust_vc_types::Seq::new(n, |i: u64| 10u64 / i);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a41_ghost_ctor_exec_param_named_is_spec_ok(n: u64) {
    let g = |i: u64| 10u64 / i;
    let _ = trust_vc_types::Seq::new(n, g);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn a42_specfn_new_exec_param_is_spec_ok() {
    let _ = trust_vc_types::Seq::<i32>::new(
        5usize,
        trust_vc_types::SpecFn::new(|i: usize| 10i32 * (i as i32)),
    );
    trust_vc::assert!(true);
}

// E24C/E24D WHAT ROUND 3'S OVERRIDE ACTUALLY PROTECTED, and where that
// protection really lives: `ClosureUseScan`. A closure that reaches a ghost
// constructor AND has any other use is still checked - the constructor argument
// is ONE ghost use, and a second use is either an instrumented call or an
// escape. Only a closure whose SOLE use is the spec constructor is skipped.
#[trust_vc::ensures(true)]
fn e24c_ghost_ctor_plus_escape_cx(n: u64, a: u64) {
    let g = |i: u64| 10u64 / i;
    let _ = trust_vc_types::Seq::new(n, g);
    let _ = g1_apply(g, a);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn e24d_ghost_ctor_plus_call_cx(n: u64) {
    let g = |i: u64| 10u64 / i;
    let _ = trust_vc_types::Seq::new(n, g);
    let _z = g(0u64);
    trust_vc::assert!(true);
}

// ---------------------------------------------------------------------------
// P7-P15 THE RECEIVERS ROUND 5 COULD ONLY FAIL CLOSED ON. Failing closed is
// sound, but round 5 landed it on the ordinary SPEC surface: a struct field
// holding a `Seq<int>` is spec code and went from `Verified` to an `unresolved
// variable` incompleteness. Two readings recover it without any new provenance:
// an UNBOUNDED MATHEMATICAL element sort (no exec container can hold one), and
// AGREEING BRANCH ARMS.
// ---------------------------------------------------------------------------
struct GhostFieldHolder {
    s: Seq<int>,
}

struct ExecFieldHolder {
    data: Vec<u64>,
}

struct NestedExecFieldHolder {
    grid: Vec<Vec<u64>>,
}

struct GhostExecElemHolder {
    s: Seq<u64>,
}

#[trust_vc::ensures(true)]
fn p7_struct_field_ghost_seq_ok(b: GhostFieldHolder) {
    let _ = b.s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p8_tuple_field_ghost_seq_ok(t: (Seq<int>, u64)) {
    let _ = t.0.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p9_if_else_ghost_ok(s1: Seq<int>, s2: Seq<int>, c: bool) {
    let _ = (if c { s1 } else { s2 }).map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p10_map_index_ghost_ok(m: Map<int, Seq<int>>, k: int) {
    let _ = m[k].map(|i| i + 1);
    trust_vc::assert!(true);
}

// THE EXEC HALF OF THE SAME TWO READINGS - both must stay CHECKED.
// P10B THE ATTRIBUTION CONTROL for P10. A `Map` INDEX carries a domain
// obligation of its own, so `m[k]` refutes with or without a closure over it.
// Pinning P10's AGREEMENT with this control is what keeps the claim honest: the
// closure is not what is being rejected.
#[trust_vc::ensures(true)]
fn p10b_map_index_no_closure_control(m: Map<int, Seq<int>>, k: int) {
    let _ = m[k];
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p11_struct_field_exec_vec_cx(b: ExecFieldHolder) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// A `Vec<Vec<u64>>` models as `Seq(Seq(Uint))`. "The element is itself a
// collection" is NOT ghost evidence, and reading it as such would hand the skip
// to an ordinary exec `Vec` of `Vec`s. This pins that boundary.
#[trust_vc::ensures(true)]
fn p12_struct_field_nested_vec_cx(b: NestedExecFieldHolder) {
    let _ = b.grid.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p13_if_else_exec_cx(v: Vec<u64>, c: bool) {
    let _ = (if c { v } else { v }).map(|x| x / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p14_match_ghost_ok(s1: Seq<int>, s2: Seq<int>, c: bool) {
    let _ = (match c {
        true => s1,
        _ => s2,
    })
    .map(|i| i + 1);
    trust_vc::assert!(true);
}

// ARM DISAGREEMENT FAILS CLOSED, in the two shapes that matter. P15: one arm
// the classifier cannot resolve (`to_vec` CONVERTS rather than preserves, so it
// is deliberately not propagated) makes the whole receiver unresolved. P15B is
// the SOUNDNESS half: a GHOST arm beside an EXEC arm must not lend the exec arm
// its skip - a join that picked either arm's reading would publish `Verified`.
#[trust_vc::ensures(true)]
fn p15_if_else_one_unresolved_arm_cx(v: Vec<u64>, c: bool) {
    let _ = (if c { v.clone() } else { v.to_vec() }).map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn p15b_if_else_ghost_and_exec_arms_cx(v: Vec<u64>, s: Seq<int>, c: bool) {
    let _ = (if c { s } else { v }).map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// X3 DISCLOSED (round 6), the residual the two new readings do NOT reach: a
// struct FIELD's origin spelling never passed the parameter seam (`StructDef`
// records modeled field types only), so a spec `Seq<u64>` field - whose elements
// are an exec-width scalar - is indistinguishable from a `Vec<u64>` field and
// fails CLOSED. Pinned as intended, not left to be rediscovered.
#[trust_vc::ensures(true)]
fn x3_struct_field_ghost_seq_exec_elem_ok(b: GhostExecElemHolder) {
    let _ = b.s.map(|i| i + 1);
    trust_vc::assert!(true);
}

// ===========================================================================
// ROUND 6b. THE MINT'S WIDTH: one definition-site frame serves EVERY
// application, so a parameter sort borrowed from ONE receiver is applied to all
// of them. Round 5 took the FIRST exec receiver's element sort and kept it.
// ===========================================================================

// M1 THE FALSE VERIFY. `x * 3` under `x < 100` is safe at `u64` and OVERFLOWS at
// `u8`. With the `Vec<u64>` use FIRST the frame mints `u64` and discharges the
// genuine `u8` obligation.
#[trust_vc::ensures(true)]
fn m1_wide_receiver_first_cx(v: Vec<u64>, w: Vec<u8>) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = v.map(g);
    let _ = w.map(g);
    trust_vc::assert!(true);
}

// M1B THE DECISIVE-PAIR TWIN: the SAME closure with the ADDED `Vec<u64>` use
// deleted. It refutes, so `m1`'s `Verified` was a check removed by ADDING A USE.
#[trust_vc::ensures(true)]
fn m1b_narrow_receiver_only_cx(v: Vec<u64>, w: Vec<u8>) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = w.map(g);
    trust_vc::assert!(true);
}

// M1C THE ORDER CONTROL: the same two uses in the other order already refuted,
// which is how the asymmetry was found.
#[trust_vc::ensures(true)]
fn m1c_narrow_receiver_first_cx(v: Vec<u64>, w: Vec<u8>) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = w.map(g);
    let _ = v.map(g);
    trust_vc::assert!(true);
}

// M2 THE HONEST TWIN at the wide receiver ALONE: `x * 3` under `x < 100` really
// is safe at `u64`, so the fix may not reject this.
#[trust_vc::ensures(true)]
fn m2_wide_receiver_only_ok(v: Vec<u64>) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = v.map(g);
    trust_vc::assert!(true);
}

// M3 THE UNRESOLVED SECOND RECEIVER, measured as the same false verify: the
// `Vec<u8>` reached through `.to_vec()` classifies UNRESOLVED, and round 5's
// rule kept the `u64` mint for it.
#[trust_vc::ensures(true)]
fn m3_unresolved_second_receiver_cx(v: Vec<u64>, w: Vec<u8>) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = v.map(g);
    let _ = w.to_vec().map(g);
    trust_vc::assert!(true);
}

// M4 OVER-REJECTION CONTROL: two receivers of the SAME element sort agree, so
// the mint survives and the honest body still verifies.
#[trust_vc::ensures(true)]
fn m4_two_same_width_receivers_ok(v: Vec<u64>, w: Vec<u64>) {
    let g = |x| x / 2u64;
    let _ = v.map(g);
    let _ = w.map(g);
    trust_vc::assert!(true);
}

// M5 OVER-REJECTION CONTROL: disagreeing widths with a body that carries no
// width-sensitive obligation still verify.
#[trust_vc::ensures(true)]
fn m5_two_widths_no_obligation_ok(v: Vec<u64>, w: Vec<u8>) {
    let g = |x| if x < 100 { x } else { 0 };
    let _ = v.map(g);
    let _ = w.map(g);
    trust_vc::assert!(true);
}

// M6 THE DISCLOSED COST of refusing to borrow a width for an application whose
// element sort is unknown: this HONEST body verified at the merge base and now
// fails closed. `m4` is the narrowing control - the cost is exactly the
// disagreeing/unresolved second receiver.
#[trust_vc::ensures(true)]
fn m6_honest_unresolved_second_receiver_rejected(v: Vec<u64>, w: Vec<u64>) {
    let g = |x| x / 2u64;
    let _ = v.map(g);
    let _ = w.to_vec().map(g);
    trust_vc::assert!(true);
}

// M7 A GHOST use may NOT veto a mint: a spec application carries no runtime
// obligation, so the exec use's sort still reaches the frame and the liar
// refutes.
#[trust_vc::ensures(true)]
fn m7_ghost_use_does_not_cancel_the_mint_cx(s: Seq<int>, w: Vec<u8>) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = s.map(g);
    let _ = w.map(g);
    trust_vc::assert!(true);
}

// ===========================================================================
// ROUND 6b RESIDUAL: `positively_ghost_element_sort` reads an `int`/`nat`/`Real`
// ELEMENT as proof of a spec collection. `int`/`nat` are TYPE ALIASES
// (`pub type int = i128;`, `pub type nat = u128;`), so `Vec<int>` is a
// constructible exec container - the justification "no exec Rust container can
// hold one" is false as written. At the PARAMETER seam the spelling saves it
// (`y2`); through a FIELD, a TUPLE or an INDEX the spelling is gone and the
// element reading hands the closure the ghost skip.
// ===========================================================================
struct IntElemVecHolder {
    data: Vec<int>,
}

#[trust_vc::ensures(true)]
fn y1_int_elem_exec_field_residual(b: IntElemVecHolder) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn y1b_int_elem_exec_field_honest_control(b: IntElemVecHolder) {
    let _ = b.data.map(|_x| 10u64 / 2u64);
    trust_vc::assert!(true);
}

// Y1C the no-sink twin: the bare literal IS checked, which is what makes `y1` an
// adding-a-use pair rather than a body nothing ever looks at.
#[trust_vc::ensures(true)]
fn y1c_int_elem_exec_field_no_sink_twin(b: IntElemVecHolder) {
    let _g = |_x| 10u64 / 0u64;
    trust_vc::assert!(true);
}

// Y2 THE INCONSISTENCY, pinned: the SAME `Vec<int>` spelled at the PARAMETER
// seam reads `CollectionOrigin::Exec` and IS checked.
#[trust_vc::ensures(true)]
fn y2_int_elem_exec_parameter_is_checked_cx(v: Vec<int>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn y2b_int_elem_exec_parameter_honest_ok(v: Vec<int>) {
    let _ = v.map(|_x| 10u64 / 2u64);
    trust_vc::assert!(true);
}

// ===========================================================================
// ROUND-6b DECISIVE-PAIR TABLE, the shapes the round-6 review swept that the
// `d`/`d6` tables did not already carry: `for_each`, `retain`, a NESTED sink, a
// sink inside a LOOP, a sink on an UNRESOLVABLE receiver, and a closure handed
// to BOTH a sink and a higher-order fn / a struct field.
// ===========================================================================

#[trust_vc::ensures(true)]
fn d7a_for_each_sink_cx(v: Vec<u64>) {
    let _ = v.for_each(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7b_retain_sink_cx(v: Vec<u64>) {
    let _ = v.retain(|_x| 10u64 / 0u64 > 1u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7c_nested_sink_cx(v: Vec<u64>, w: Vec<u64>) {
    let _ = v.map(|x: u64| {
        let _ = w.map(|_y| 10u64 / 0u64);
        x
    });
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7c_nested_no_sink_twin(v: Vec<u64>, w: Vec<u64>) {
    let _ = v.map(|x: u64| {
        let _g = |_y| 10u64 / 0u64;
        x
    });
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7d_sink_inside_a_loop_cx(v: Vec<u64>, n: u64) {
    let mut i = 0u64;
    while i < n {
        let _ = v.map(|_x| 10u64 / 0u64);
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7d_loop_no_sink_twin(v: Vec<u64>, n: u64) {
    let mut i = 0u64;
    while i < n {
        let _g = |_x| 10u64 / 0u64;
        i = i + 1u64;
    }
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7e_unresolvable_receiver_sink_cx(v: Vec<u64>) {
    let _ = v.to_vec().map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7f_sink_and_higher_order_cx(v: Vec<u64>, a: u64) {
    let g = |_x| 10u64 / 0u64;
    let _ = v.map(g);
    let _ = g1_apply(g, a);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7f_higher_order_only_twin(v: Vec<u64>, a: u64) {
    let g = |_x| 10u64 / 0u64;
    let _ = g1_apply(g, a);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7g_sink_and_struct_field_cx(v: Vec<u64>) {
    let g = |_x| 10u64 / 0u64;
    let _ = v.map(g);
    let _h = Holder { f: g };
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7g_struct_field_only_twin(v: Vec<u64>) {
    let g = |_x| 10u64 / 0u64;
    let _h = Holder { f: g };
    trust_vc::assert!(true);
}

// A GHOST sink plus an EXEC sink on ONE literal: the exec use must still be
// checked, i.e. a ghost use may not launder a closure that also escapes to exec.
#[trust_vc::ensures(true)]
fn d7h_ghost_and_exec_sink_cx(s: Seq<int>, v: Vec<u64>) {
    let g = |_x| 10u64 / 0u64;
    let _ = s.map(g);
    let _ = v.map(g);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn d7h_ghost_sink_only_twin(s: Seq<int>, v: Vec<u64>) {
    let g = |_x| 10u64 / 0u64;
    let _ = s.map(g);
    trust_vc::assert!(true);
}

// ===========================================================================
// ROUND 7: FIELD-LEVEL COLLECTION PROVENANCE. The origin spelling of a STRUCT
// FIELD and of a TUPLE COMPONENT is now recorded the way the parameter seam
// records a binding's, so the field/tuple/index routes read a MEASUREMENT
// instead of round 6's element-sort guess. Both halves of that guess are
// fixtured here: the FALSE VERIFY it granted (`z1`-`z4`, `y1`) and the
// OVER-REJECTION its absence forced (`x3`, `z3b`, `z7b`).
// ===========================================================================
struct NatElemVecHolder {
    data: Vec<nat>,
}

struct IntElemSetHolder {
    data: BTreeSet<int>,
}

struct MultiWidthHolder {
    wide: Vec<u64>,
    narrow: Vec<u8>,
}

struct NestedExecHolder {
    inner: ExecFieldHolder,
}

struct NestedGhostHolder {
    inner: GhostFieldHolder,
}

type AliasedVec = Vec<u64>;

struct AliasFieldHolder {
    data: AliasedVec,
}

// Z1 a `Vec<nat>` FIELD. `nat` is `pub type nat = u128;`, so this is an exec
// container and the closure over it carries a real obligation.
#[trust_vc::ensures(true)]
fn z1_nat_elem_exec_field_cx(b: NatElemVecHolder) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// Z2 a `BTreeSet<int>` FIELD: the same reading through the `Set` sort, which has
// no bounded-length bit of its own.
#[trust_vc::ensures(true)]
fn z2_int_elem_exec_set_field_cx(b: IntElemSetHolder) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// Z3 a `(Vec<int>, u64)` TUPLE COMPONENT. A tuple carrier's NAME is built from
// its MODELED element types, so `(Vec<int>, u64)` and `(Seq<int>, u64)` name the
// same carrier - which is why the component provenance is keyed by the BINDING.
#[trust_vc::ensures(true)]
fn z3_int_elem_exec_tuple_cx(t: (Vec<int>, u64)) {
    let _ = t.0.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// Z3B/Z3C THE TUPLE DECISIVE PAIR, and the over-rejection half at the tuple
// seam: ONE body, ONE element width, TWO spellings. The spec component is a
// spec function and verifies; the exec component is checked and refutes on the
// `u64` overflow of `i + 1`.
#[trust_vc::ensures(true)]
fn z3b_ghost_seq_u64_tuple_ok(t: (Seq<u64>, u64)) {
    let _ = t.0.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn z3c_exec_vec_u64_tuple_cx(t: (Vec<u64>, u64)) {
    let _ = t.0.map(|i| i + 1);
    trust_vc::assert!(true);
}

// Z4 THE INDEX ROUTE, which round 6b's residual named but did not fixture: a
// `Vec<Vec<int>>` indexed once has an `int` element, so the retired reading
// handed `m[i].map(..)` the ghost skip on an ordinary exec container of
// containers.
#[trust_vc::ensures(true)]
fn z4_index_int_elem_exec_cx(m: Vec<Vec<int>>, i: usize) {
    let _ = m[i].map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// Z5 THE FAIL-CLOSED DISCLOSURE: a field spelled through a TYPE ALIAS matches
// neither positive table, so its provenance stays `Unknown` and the body is
// CHECKED. Over-rejection, which is the acceptable direction.
#[trust_vc::ensures(true)]
fn z5_alias_field_unknown_provenance_cx(b: AliasFieldHolder) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// Z6 THE MULTI-WIDTH SHAPE ROUND 6b CLOSED, APPLIED THROUGH FIELDS. Before this
// round a field receiver minted NOTHING, so the shape could not even arise
// there; now that fields mint, round 6b's pairwise agreement has to cover them.
// `z6` is `z6b` plus one ADDED use and must not be weaker for it.
#[trust_vc::ensures(true)]
fn z6_multiwidth_field_cx(b: MultiWidthHolder) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = b.wide.map(g);
    let _ = b.narrow.map(g);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn z6b_multiwidth_field_narrow_only_cx(b: MultiWidthHolder) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = b.narrow.map(g);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn z6c_multiwidth_field_reversed_cx(b: MultiWidthHolder) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = b.narrow.map(g);
    let _ = b.wide.map(g);
    trust_vc::assert!(true);
}

// Z6D THE NARROWING CONTROL: the wide field ALONE still mints and still
// verifies, so `z6` measures the disagreement and not a blanket refusal to mint
// through a field.
#[trust_vc::ensures(true)]
fn z6d_multiwidth_field_wide_only_ok(b: MultiWidthHolder) {
    let g = |x| if x < 100 { x * 3 } else { 0 };
    let _ = b.wide.map(g);
    trust_vc::assert!(true);
}

// Z7 A TWO-STEP PROJECTION: the walk resolves the carrier of EACH step and the
// LAST step decides, in both directions.
#[trust_vc::ensures(true)]
fn z7_nested_exec_field_cx(b: NestedExecHolder) {
    let _ = b.inner.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn z7b_nested_ghost_field_ok(b: NestedGhostHolder) {
    let _ = b.inner.s.map(|i| i + 1);
    trust_vc::assert!(true);
}

// X3B THE FIELD DECISIVE PAIR for the over-rejection half (see `x3`): ONE body,
// ONE element width, TWO spellings. `Seq<u64>` is spec and verifies; `Vec<u64>`
// is exec, mints `u64`, and refutes on the overflow of `i + 1`.
#[trust_vc::ensures(true)]
fn x3b_exec_vec_u64_field_same_body_cx(b: ExecFieldHolder) {
    let _ = b.data.map(|i| i + 1);
    trust_vc::assert!(true);
}

// Y1D THE NARROWING CONTROL for `y1b`'s disclosed cost: the identical honest
// body over a field whose element sort IS mintable verifies, so the cost is
// exactly the unmintable `int`/`nat` element and not the exec field reading.
#[trust_vc::ensures(true)]
fn y1d_u64_elem_exec_field_honest_ok(b: ExecFieldHolder) {
    let _ = b.data.map(|_x| 10u64 / 2u64);
    trust_vc::assert!(true);
}

// Z5B/Z5C WHAT RETIRING THE ELEMENT-SORT READING RE-OPENS, measured rather than
// left to surface in review. The retired reading recovered ANY receiver with an
// `int`/`nat`/`Real` element, including spec ones whose SPELLING is invisible.
// Field-level provenance recovers the ones spelled `Seq`/`Set`/`Map`/`Multiset`
// directly; a spec collection reached through a TYPE ALIAS still has no
// recorded spelling, so it now fails CLOSED. That is an over-rejection, which is
// the acceptable direction, and it is the ONLY thing the retirement costs that
// round 7 does not give back.
type GhostAliasedSeq = Seq<int>;

struct GhostAliasFieldHolder {
    data: GhostAliasedSeq,
}

#[trust_vc::ensures(true)]
fn z5b_alias_ghost_field_over_rejection(b: GhostAliasFieldHolder) {
    let _ = b.data.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn z5c_alias_ghost_parameter_over_rejection(s: GhostAliasedSeq) {
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

// ===========================================================================
// ROUND 7 REVIEW: WHAT THE RETIREMENT COSTS BESIDES THE ALIAS.
//
// `z5b`/`z5c` pin the TYPE ALIAS as the price of retiring the element-sort
// reading, and the round-7 commit calls it "the ONLY thing the retirement costs
// that round 7 does not give back". MEASURED, that is not so. Restoring the
// retired reading and nothing else (the `G13` neutralization) turns each of the
// four fixtures below from a non-verify back into `Verified`, so each is a spec
// receiver round 6 recovered and round 7 does not: a GENERIC carrier whose
// field spelling is the type PARAMETER (`data: T`, so no spelling reaches the
// source-struct seam), and a TUPLE nested below the root binding — reached
// either through another tuple or through a struct FIELD, neither of which the
// binding-keyed component table can name.
//
// They are OVER-REJECTIONS, which is the acceptable direction, and each is
// pinned WITH its exec twin so the pin can never be satisfied by a blanket
// "generic and nested receivers are ghost": `v1b` and `v4b` are the identical
// shapes holding an exec `Vec<int>` and must stay checked.
// ===========================================================================
struct GenericFieldHolder<T> {
    data: T,
}

struct TupleFieldGhostHolder {
    t: (Seq<int>, u64),
}

struct TupleFieldExecHolder {
    t: (Vec<int>, u64),
}

// V1 a GENERIC carrier holding a spec `Seq<int>`: the field's spelling is `T`,
// which matches neither positive table, so provenance is `Unknown` and the body
// is checked.
#[trust_vc::ensures(true)]
fn v1_generic_carrier_spec_seq_field_over_rejection(b: GenericFieldHolder<Seq<int>>) {
    let _ = b.data.map(|i| i + 1);
    trust_vc::assert!(true);
}

// V1B THE EXEC TWIN, and the reason `v1` is a disclosure rather than a licence:
// the identical carrier holding an exec `Vec<int>` must stay CHECKED. Under the
// retired reading this one was a false `Verified`.
#[trust_vc::ensures(true)]
fn v1b_generic_carrier_exec_vec_field_cx(b: GenericFieldHolder<Vec<int>>) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// V2 the same generic carrier holding a spec `Map<int, int>`.
#[trust_vc::ensures(true)]
fn v2_generic_carrier_spec_map_field_over_rejection(b: GenericFieldHolder<Map<int, int>>) {
    let _ = b.data.map_values(|v| v + 1);
    trust_vc::assert!(true);
}

// V3 a TUPLE NESTED BELOW THE ROOT BINDING. The component table is keyed by the
// binding and splits at depth zero only, so `t.0.0` reads `Unknown`.
#[trust_vc::ensures(true)]
fn v3_nested_tuple_spec_seq_over_rejection(t: ((Seq<int>, u64), u64)) {
    let _ = t.0 .0.map(|i| i + 1);
    trust_vc::assert!(true);
}

// V4 a TUPLE REACHED THROUGH A STRUCT FIELD. The field table records the
// field's own spelling (`(Seq<int>,u64)`, which matches neither positive table)
// and there is no per-component entry for a tuple that is not the root binding,
// so this reads `Unknown` too. Note what this refutes: `z5b`'s claim that "the
// cost is the alias and not the field".
#[trust_vc::ensures(true)]
fn v4_tuple_in_struct_field_spec_over_rejection(b: TupleFieldGhostHolder) {
    let _ = b.t.0.map(|i| i + 1);
    trust_vc::assert!(true);
}

// V4B THE EXEC TWIN of `v4`, a false `Verified` under the retired reading.
#[trust_vc::ensures(true)]
fn v4b_tuple_in_struct_field_exec_cx(b: TupleFieldExecHolder) {
    let _ = b.t.0.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ===========================================================================
// ROUND-7 REVIEW: THE PROJECTION ROOT WAS NOT SHADOW-GUARDED.
//
// Round 7 records provenance against the DECLARED binding — the per-(carrier,
// field) table is keyed by the carrier `get_variable_type` answers with, and the
// per-(binding, index) tuple table is keyed by the binding NAME — while the sink
// scan is FLAT over the whole body. Nothing re-resolved the root, so a `let`
// that REBINDS it had the parameter's recorded spelling answer for an unrelated
// value. Measured at 7119a236, cache off: every `zzs1`-`zzs4b` below came back
// `Verified` on a body that ALWAYS divides by zero.
//
// `zzs1b`/`zzs1c` are the decisive controls and they are what makes this a
// defect rather than an opinion: the SAME body with the shadowed parameter
// RENAMED (`zzs1b`) or DELETED (`zzs1c`) was a non-verify at the same commit, so
// the skip was bought by the NAME of an otherwise unused parameter.
//
// `zzs5`-`zzs8` are the narrowing controls in the other direction, so the guard
// cannot be satisfied by refusing every projection: an UNSHADOWED spec tuple
// component and an unshadowed spec field are still legitimately skipped (a spec
// closure is not checked for panic-freedom), and a purely LOCAL carrier resolved
// no field before the guard either — which is the measurement that says the
// guard costs nothing.
// ===========================================================================
struct ZzsGhostH {
    data: Seq<u64>,
}

struct ZzsExecH {
    data: Vec<u64>,
}

fn zzs_mk_exec(w: Vec<u64>) -> ZzsExecH {
    ZzsExecH { data: w }
}

#[trust_vc::ensures(true)]
fn zzs1_tuple_shadow_spec_then_exec_cx(t: (Seq<u64>, u64), w: Vec<u64>) {
    let t = (w, 1u64);
    let _ = t.0.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zzs1b_shadow_control_param_renamed_cx(u: (Seq<u64>, u64), w: Vec<u64>) {
    let t = (w, 1u64);
    let _ = t.0.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zzs1c_shadow_control_no_tuple_param_cx(w: Vec<u64>) {
    let t = (w, 1u64);
    let _ = t.0.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZZS2 an EXPLICIT exec annotation on the shadowing `let` loses to the
// parameter seam too, which is what says the hole is the ROOT and not the
// classifier's handling of an un-annotated initializer.
#[trust_vc::ensures(true)]
fn zzs2_tuple_shadow_annotated_cx(t: (Seq<u64>, u64), w: Vec<u64>) {
    let t: (Vec<u64>, u64) = (w, 1u64);
    let _ = t.0.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZZS3 THE STRUCT-CARRIER TWIN: the same hole, on the OTHER table. It refutes
// the reading that this is a consequence of the tuple table's binding key —
// both tables speak for the declared binding.
#[trust_vc::ensures(true)]
fn zzs3_struct_shadow_cx(b: ZzsGhostH, w: Vec<u64>) {
    let b = zzs_mk_exec(w);
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zzs4_tuple_shadow_inner_block_cx(t: (Seq<u64>, u64), w: Vec<u64>) {
    {
        let t = (w, 1u64);
        let _ = t.0.map(|_x| 10u64 / 0u64);
    }
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zzs4b_tuple_shadow_index_one_cx(t: (u64, Seq<u64>, u64), w: Vec<u64>) {
    let t = (0u64, w, 1u64);
    let _ = t.1.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZZS5/ZZS6 THE NARROWING CONTROLS. An UNSHADOWED spec receiver is still
// skipped: a spec closure carries no panic-freedom obligation, which is the
// capability `zzs1`-`zzs4b` were stealing rather than exercising.
#[trust_vc::ensures(true)]
fn zzs5_unshadowed_ghost_tuple_ok(t: (Seq<u64>, u64)) {
    let _ = t.0.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zzs6_unshadowed_ghost_field_ok(b: ZzsGhostH) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZZS7/ZZS8 WHAT THE GUARD COSTS, measured: a purely LOCAL carrier — no
// parameter of that name at all — resolved no field provenance BEFORE the guard
// either, so failing closed on a let-bound root takes nothing away.
#[trust_vc::ensures(true)]
fn zzs7_local_carrier_ghost_field_over_rejection(s: Seq<u64>) {
    let b = ZzsGhostH { data: s };
    let _ = b.data.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zzs8_local_tuple_ghost_over_rejection(s: Seq<u64>) {
    let t = (s, 1u64);
    let _ = t.0.map(|i| i + 1);
    trust_vc::assert!(true);
}

// ZZS9 the USE BEFORE the rebind, which was never affected and stays checked.
#[trust_vc::ensures(true)]
fn zzs9_use_before_shadow_cx(t: (Vec<u64>, u64), s: Seq<u64>) {
    let _ = t.0.map(|_x| 10u64 / 0u64);
    let t = (s, 1u64);
    trust_vc::assert!(true);
}

// ===========================================================================
// ZT (ROUND-8 PROBES): a shadow that is not a `let` IDENT.
// ===========================================================================
struct ZtGhostH {
    data: Seq<u64>,
}

struct ZtExecH {
    data: Vec<u64>,
}

fn zt_mk_exec(w: Vec<u64>) -> ZtExecH {
    ZtExecH { data: w }
}

#[trust_vc::ensures(true)]
fn zt1_path_tuple_pat_shadow_cx(v: Seq<u64>, w: Vec<u64>) {
    let (v, _z) = (w, 0u64);
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt1b_path_tuple_pat_control_renamed_cx(u: Seq<u64>, w: Vec<u64>) {
    let (v, _z) = (w, 0u64);
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt1c_path_tuple_pat_control_no_param_cx(w: Vec<u64>) {
    let (v, _z) = (w, 0u64);
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt2_field_tuple_pat_shadow_cx(t: (Seq<u64>, u64), w: Vec<u64>) {
    let (t, _z) = ((w, 1u64), 0u64);
    let _ = t.0.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt3_struct_tuple_pat_shadow_cx(b: ZtGhostH, w: Vec<u64>) {
    let (b, _z) = (zt_mk_exec(w), 0u64);
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt4_path_match_binding_shadow_cx(v: Seq<u64>, w: Vec<u64>) {
    match w {
        v => {
            let _ = v.map(|_x| 10u64 / 0u64);
        }
    }
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt5_field_match_binding_shadow_cx(t: (Seq<u64>, u64), p: (Vec<u64>, u64)) {
    match p {
        t => {
            let _ = t.0.map(|_x| 10u64 / 0u64);
        }
    }
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt6_path_closure_param_shadow_cx(v: Seq<u64>) {
    let h = |v: Vec<u64>| {
        let _ = v.map(|_x| 10u64 / 0u64);
        0u64
    };
    let _ = g1_apply(h, 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt7_path_for_binding_shadow_cx(v: Seq<u64>, ws: Vec<Vec<u64>>) {
    for v in ws {
        let _ = v.map(|_x| 10u64 / 0u64);
    }
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt8_field_nested_tuple_pat_shadow_cx(b: ZtGhostH, w: Vec<u64>) {
    let (_z, (b, _y)) = (0u64, (zt_mk_exec(w), 1u64));
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt9_path_struct_pat_shadow_cx(v: Seq<u64>, e: ZtExecH) {
    let ZtExecH { data: v } = e;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt10_path_nested_fn_param_shadow_cx(v: Seq<u64>) {
    fn zt_inner(v: Vec<u64>) {
        let _ = v.map(|_x| 10u64 / 0u64);
    }
    zt_inner(Vec::new());
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt11_field_nested_fn_param_shadow_cx(b: ZtGhostH) {
    fn zt_inner2(b: ZtExecH) {
        let _ = b.data.map(|_x| 10u64 / 0u64);
    }
    zt_inner2(zt_mk_exec(Vec::new()));
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt12_fold_accum_ident_shadow_cx(v: Vec<u8>, a: u64) {
    let a = 200u8;
    let _ = v.fold(a, |acc, x| acc + 200u8);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt12b_fold_accum_control_renamed_cx(v: Vec<u8>, q: u64) {
    let a = 200u8;
    let _ = v.fold(a, |acc, x| acc + 200u8);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt13_fold_accum_destructure_shadow_cx(v: Vec<u8>, a: u64, p: (u8, u64)) {
    let (a, _z) = p;
    let _ = v.fold(a, |acc, x| acc + 200u8);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt12c_fold_accum_param_seed_cx(v: Vec<u8>, a: u8) {
    let _ = v.fold(a, |acc, x| acc + 200u8);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt12d_fold_accum_param_seed_ok(v: Vec<u8>, a: u8) {
    let _ = v.fold(a, |acc, x| acc / 2u8);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt12e_fold_accum_shadow_in_other_scope_cx(v: Vec<u8>, a: u8) {
    {
        let a = 1u64;
        let _ = a;
    }
    let _ = v.fold(a, |acc, x| acc + 200u8);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt14_destructuring_binder_other_name_ok(s: Seq<u64>, p: (Vec<u64>, u64)) {
    let (w, _z) = p;
    let _ = w;
    let _ = s.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt15_match_binder_other_name_ok(s: Seq<u64>, p: (Vec<u64>, u64)) {
    match p {
        q => {
            let _ = q;
        }
    }
    let _ = s.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt16_field_destructuring_binder_other_name_ok(b: ZtGhostH, p: (Vec<u64>, u64)) {
    let (w, _z) = p;
    let _ = w;
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt17_closure_param_shares_receiver_name(s: Seq<u64>) {
    let _ = s.map(|s| s + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zt18_for_binding_shares_receiver_name(s: Seq<u64>, ws: Vec<u64>) {
    for s in ws {
        let _ = s;
    }
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

// ===========================================================================
// ZU (ROUND-9 PROBES): the flat `let` map SPOKE FOR A DECLARED NAME, and an
// `@` pattern binds more than its head.
//
// Round 5's shadow rule fires only on a DISAGREEMENT between the declared sort
// and the recorded `let` sort. When the declared sort is `Unresolved` the rule
// deliberately let the `let` answer — and a DECLARED parameter reads
// `Unresolved` whenever its collection is reached through a TYPE ALIAS (round
// 7's `z5c`). The scan is flat over the whole body, so ANY `let` of that name,
// in ANY scope and at ANY position, then supplied a POSITIVE ghost reading for
// an exec parameter.
// ===========================================================================
type ZuAliasVec = Vec<u64>;

#[trust_vc::ensures(true)]
fn zu1_alias_param_block_scope_ghost_let_cx(v: ZuAliasVec) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZU1B/ZU1C THE DECISIVE CONTROLS: the identical body with the inner `let`
// RENAMED, and with the inner block DELETED. Both were non-verifies at
// `16240019`, so what bought the skip was an UNRELATED statement in a scope the
// receiver is not in.
#[trust_vc::ensures(true)]
fn zu1b_alias_param_control_inner_let_renamed_cx(v: ZuAliasVec) {
    {
        let q: Seq<u64> = Seq::empty();
        let _ = q;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu1c_alias_param_control_no_inner_let_cx(v: ZuAliasVec) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu2_alias_param_closure_scope_ghost_let_cx(v: ZuAliasVec) {
    let h = |_q: u64| {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
        0u64
    };
    let _ = g1_apply(h, 0u64);
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu3_alias_param_match_arm_ghost_let_cx(v: ZuAliasVec, c: u64) {
    match c {
        _ => {
            let v: Seq<u64> = Seq::empty();
            let _ = v;
        }
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu4_alias_param_later_ghost_let_cx(v: ZuAliasVec) {
    let _ = v.map(|_x| 10u64 / 0u64);
    let v: Seq<u64> = Seq::empty();
    let _ = v;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu5_alias_param_adapter_ghost_let_cx(v: ZuAliasVec) {
    {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.iter().map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu6_alias_param_for_body_ghost_let_cx(v: ZuAliasVec, ws: Vec<u64>) {
    for _w in ws {
        let v: Seq<u64> = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu7_alias_param_unannotated_ghost_let_cx(v: ZuAliasVec) {
    {
        let v = Seq::empty();
        let _ = v;
    }
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZU8/ZU8B THE LIAR TWIN for the round-9 guard, and what keeps it from being
// satisfiable by silencing the `let` map altogether. A TRUE BODY LOCAL — a name
// the context declares NOTHING for — must still be classified by its own `let`,
// which is round 6's recovery. ONE body, ONE element width, TWO spellings.
#[trust_vc::ensures(true)]
fn zu8_body_local_ghost_let_ok() {
    let s: Seq<u64> = Seq::empty();
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu8b_body_local_exec_let_cx() {
    let s: Vec<u64> = Vec::new();
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

// ZU9 an `@` PATTERN BINDS MORE THAN ITS HEAD. `local_ident` answers for the
// head, so the classifiable half took `q` and the opaque half — the only thing
// that records the other binders — never ran.
#[trust_vc::ensures(true)]
fn zu9_at_subpattern_shadow_cx(v: Seq<u64>, p: (Vec<u64>, u64)) {
    let q @ (v, _z) = p;
    let _ = q;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zu9b_at_subpattern_control_renamed_cx(u: Seq<u64>, p: (Vec<u64>, u64)) {
    let q @ (v, _z) = p;
    let _ = q;
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZU10 THE LIAR TWIN for the `@` half: a subpattern binding SOME OTHER name
// must leave the spec receiver alone. Only the NAME may distinguish it from
// `zu9`.
#[trust_vc::ensures(true)]
fn zu10_at_subpattern_other_name_ok(s: Seq<u64>, p: (Vec<u64>, u64)) {
    let q @ (w, _z) = p;
    let _ = q;
    let _ = w;
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

// ZU11 WHAT THE `@` HALF COSTS, measured: the binder set is flat, so a
// subpattern that merely SHARES the receiver's name fails closed. Same class as
// `zt17`/`zt18`, and the re-key signal if a future round scopes the map.
#[trust_vc::ensures(true)]
fn zu11_at_subpattern_shares_receiver_name(s: Seq<u64>, p: (Vec<u64>, u64)) {
    let q @ (s, _z) = p;
    let _ = q;
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}
