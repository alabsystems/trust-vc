// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for the ESCAPING-CLOSURE body
//! panic-freedom hole (#2778 residual).
//!
//! THE DEFECT, measured on main: closure-body panic-freedom was instrumented
//! ONLY at a DIRECT LOCAL CALL SITE `g(args)`
//! (`maybe_emit_invoked_exec_closure_arith_safety`). A closure that ESCAPES had
//! its body checked NOWHERE, so
//!
//! ```ignore
//! let g = |x: u64| x / 0u64;   // ALWAYS divides by zero
//! g1_apply(g, a)               // fn g1_apply(g: impl Fn(u64) -> u64, a: u64)
//! ```
//!
//! returned `Verified`. Nine escape routes were probed and six were measured
//! false-`Verified`: higher-order argument, inline argument literal, struct
//! field, tuple, shadowed-before-any-call, and never-called-at-all (the other
//! three failed closed for UNRELATED reasons — return-value lowering and an
//! `unresolved variable` incompleteness). The direct-call control on the same
//! closure fails closed, which is why the existing
//! `crates/trust-vc-core/src/vc_extraction/tests/closure_body_soundness.rs`
//! suite could not see any of it: every one of its fixtures calls the closure
//! directly.
//!
//! THE FIX: a closure body is checked WHERE IT IS DEFINED. Its obligations
//! belong to the enclosing function at the definition site, under the path
//! condition that reaches the definition (`e11`/`a7`), over the closure's OWN
//! FRAME — parameters are FRESH unconstrained symbols of their written sorts
//! (`e10`) and captures resolve to their definition-site values (`a8`), with no
//! enclosing fact reaching a parameter that merely shares a name (`e12`).
//! `plan_closure_def_site_checks` decides which literals need it, so the
//! strictly more precise direct-call lane keeps covering a closure whose every
//! use is a covering call (`a4`) and a ghost/spec closure is never instrumented
//! (`a6`).
//!
//! EVERY pin here has a twin. Each `_cx` liar has an `_ok` honest partner of the
//! SAME shape, so a fix that simply rejected more could not pass this file.
//!
//! ROUND 2 closed four more routes the first increment left open, each measured
//! false-`Verified` before the fix and each with a reproduced single-pin
//! neutralization:
//!
//!   * `e15`/`e16` — the ghost/spec skip was keyed on the METHOD NAME alone, so
//!     every exec `.map`/`.filter`/`.fold` closure was skipped. The modeled type
//!     cannot separate a ghost `Seq` from an exec `Vec`, so the discriminator is
//!     the CLOSURE: a literal whose parameters carry written finite-width scalar
//!     types is exec.
//!   * `e17` — the definition-site check modeled ONE application from the
//!     capture's definition-site value, so an `FnMut` that zeroes its own
//!     divisor passed. A capture the body WRITES is arbitrary on body entry.
//!   * `e18` — a closure literal written inline as an argument to a modeled
//!     collection mutator (`v.push(|x, y| x / y)`) was never visited at all.
//!   * `e19` — a closure DEFINED inside a loop was deferred by the emitter and
//!     covered by no call site either.
//!
//! and pinned the `assume` rule in both directions: `h7g`/`h7h` (an in-body
//! `assume!` reaches only the obligations it DOMINATES, and a nested closure's
//! hypothesis is not this body's) against `a15` (an in-body `assume!` that
//! genuinely establishes the divisor still discharges the body's division).
//!
//! WHAT EACH PIN ACTUALLY DISCRIMINATES, measured by neutralizing ONE guard at a
//! time and recorded so the next sweep does not re-derive it:
//!   * `emit_closure_def_site_body_safety` -> no-op: exactly 15 red
//!     (`e1`-`e4`, `e6`, `e8`-`e15`, `e18`, `e19`).
//!   * the re-entrancy freshening -> no-op: exactly `e17`.
//!   * the exec-typed-parameter gate -> name-only: exactly `e15`.
//!   * the inline-literal argument visit -> removed: exactly `e18`.
//!   * the emitter's loop-context bail -> restored: exactly `e19`.
//!   * `scope_closure_body_obligations` -> no-op: exactly `h7`, `h7f`.
//!   * the hypothesis ORDER (all body assumptions conjoined up front instead of
//!     only the ones preceding each assertion): exactly `h7d`.
//!
//! Pins NOT discriminated by any of those, and kept as ratchets rather than as
//! evidence: `e5`, `e7` (already fail-closed for unrelated reasons — return-value
//! lowering, and an `unresolved variable` incompleteness), `h7c`, `h7e`, `h7g`,
//! `h7h`.
//!
//! ROUND 3 closed the route that made the whole lane disable-able, plus the
//! ghost-CONSTRUCTOR twin of round 2's method finding:
//!
//!   * `e20`-`e23` / `a17`-`a19` — a write to the closure local was treated as a
//!     KILL unconditionally, so a rebind on ONE arm of an `if` (or in an `else`,
//!     a `match` arm, or a loop body) made the later `g(a, 0)` the only
//!     classified use and the DEFINITION site emitted nothing, while
//!     `reapply_common_branch_exec_closure_rebinds` had already cleared
//!     `exec_closure_defs["g"]` for a one-arm rebind so the CALL site emitted
//!     nothing either. `e20b` is the decisive pair: the identical function with
//!     the call DELETED counterexamples, i.e. ADDING A USE made an unchecked
//!     closure LESS checked. A write is now a kill only when it is
//!     UNCONDITIONAL — and an unconditional kill is itself coverage, which
//!     RESTORED `a18` (a straight-line rebind whose only live body is safe),
//!     measured as an over-rejection of the first increment.
//!   * `e24`/`e25` / `a20` — `ghost_closure_sink_call` keyed the spec skip on the
//!     CALLEE PATH alone, so `Seq::new(n, |i: u64| 10u64 / i)` (and its named
//!     spelling) was skipped by the planner and reached no call site. The
//!     constructor sink now uses the same exec-typed-parameter discriminator the
//!     METHOD sink got in round 2; `a6`/`a6b` (untyped and `int`-typed spec
//!     closures) are untouched.
//!
//! ROUND-3 NEUTRALIZATIONS, each measured by disabling ONE guard:
//!   * the conditional-write rule -> unconditional KILL again: exactly `e20`,
//!     `e20b`, `e21`, `e22`, `e23`.
//!   * the `dead`-is-coverage clause -> removed: exactly `a18`, `a19` here and
//!     `c_closure_rebind_block_safe_true` / `c_closure_rebind_if_safe_true` in
//!     `be_frame_round8_soundness` — which is the measurement that settles what
//!     those two round-8 fixtures pin: a REAL CAPABILITY (an unconditionally
//!     dead literal carries no obligation), not the hole.
//!   * the both-arms-unconditional exception -> removed: exactly `a19` here and
//!     `c_closure_rebind_if_safe_true` there.
//!   * the constructor sink's exec-typed gate -> path-only: exactly `e24`, `e25`.
//!   * the sibling-arm kill-stop suppression -> removed (the first arm's write
//!     ends the scan again): exactly `e26`.
//!
//! ROUND 3b is a hole ROUND 3 ITSELF OPENED and closed in the same increment,
//! recorded rather than quietly folded in: "an unconditional kill ends the
//! scan" is right along a path and wrong across a branch, because the two arms
//! of an `if`/`else` are ALTERNATIVES. Measured false-`Verified` (`e26`) before
//! the suppression, with the arm ORDER as the trigger.
//!
//! TWO DISCLOSED CAPABILITY REGRESSIONS, pinned rather than hidden. The second
//! (`x2`/`x2b` against `x2c`) is round 5's, and it is the direct price of
//! failing CLOSED on an unresolvable receiver: an untyped closure parameter at a
//! receiver whose element sort is unknown has nothing to mint, so the HONEST
//! body is rejected too (`(if c { v } else { v }).map(|x| x / 2u64)` and the
//! chained `v.map(|x: u64| x).map(|x| x / 2u64)` both come back an `unresolved
//! variable` incompleteness). `x2c` is the narrowing control: the identical
//! honest body at a receiver the classifier DOES resolve still verifies, so the
//! cost is exactly the unresolvable receiver and nothing wider.
//!
//! The first (`x1`/`x1b`
//! against `a21`): a definition-site check ranges over an ARBITRARY parameter,
//! so unguarded `x + 1` in an escaping exec closure is refutable and
//! `v.map(|x: u64| x + 1u64)` — `Verified` at the merge base only because
//! nothing checked the body — is now rejected. It is not narrowable: any fact
//! that would discharge it is a fact `e10`/`e12` forbid the frame from having.
//! Guarding the arithmetic in the body verifies (`a21`). Measured for `+`, `*`,
//! the ghost-constructor `+` and — round 4, a fourth instance round 3 did not
//! name — `-` (`x1c`).
//!
//! MEASURED RESIDUALS, not closed here. ROUND 4 CORRECTED THEIR SCOPE (round 3's
//! wording understated it in two measured ways) and made every repro EXECUTABLE
//! — see `assert_same_verdict` and the `residual_*` tests:
//!   * ROUTE A — CLOSED ON THE EXEC SIDE IN ROUND 5 FOR `Vec`/slice/array AND
//!     IN ROUND 6 FOR THE REST. The round-3/4 text that
//!     stood here SAID LESS THAN THE TRUTH and is corrected rather than
//!     rewritten away. It described route A as a body "checked nowhere", which
//!     is true only at the MERGE BASE. On this branch the definition-site lane
//!     checks an escaping closure's body, so route A meant the body is checked
//!     UNTIL A SINK IS ADDED: handing an otherwise-CHECKED literal to
//!     `.map`/`.filter`/`.fold` or to a ghost constructor turned a refutation
//!     back into a `Verified` whenever its parameter list was not FULLY written
//!     in exec scalar types. That is an ADDING-A-USE-DISABLES-THE-CHECK route
//!     with a decisive pair, i.e. the very pattern this campaign declared a
//!     BLOCKER in the rebind family (`e20b`, `e27b`), and it was wider than
//!     "untyped": a PARTIALLY annotated list kept the skip too
//!     (`v.fold(0u64, |acc: u64, x| acc / 0u64)`, `u1c`).
//!
//!     ROUND 5's FIX is the one round 3 named and did not attempt: the skip now
//!     reads THE RECEIVER, not the parameter list. Only a receiver that resolves
//!     as a ghost/spec collection buys the skip; an EXEC receiver is checked
//!     with its modeled ELEMENT sort minted for the unwritten parameters (which
//!     is what makes the probe a REFUTATION instead of the `Error` round 3
//!     measured — `n2` pins exactly that), and an UNRESOLVED receiver is checked
//!     too, FAIL CLOSED (`n7`). The provenance comes from
//!     `VariableDecl::bounded_len`, the one place a `Vec` and a `Seq` are still
//!     distinguishable after both collapse to `TrustVcType::Seq`. `u1`/`u1c` are
//!     RE-KEYED from agreement pins to verdict pins, exactly as round 4 said
//!     they should be the day they moved.
//!
//!     ROUND 5'S FIX WAS NOT COMPLETE, AND ROUND 6 FINISHES IT. Round 5 read
//!     ONE provenance bit (`bounded_len`) and treated its ABSENCE as ghost, so
//!     the exec side of route A stayed OPEN in the containers that have no such
//!     bit: `BTreeSet<u64>`/`HashSet<u64>` parse to `TrustVcType::Set` and
//!     `BTreeMap`/`HashMap` to `Map`, so `v.map(|_x| 10u64 / 0u64)` on an exec
//!     `BTreeSet` published `Verified` while its no-sink twin refuted — the
//!     blocker pattern, on the exec side the branch declared closed, and in
//!     PROSE ONLY with no fixture and no pin. Round 5's stated defence (failing
//!     closed would reject the `Set`/`Map` spec surface) was a FALSE DICHOTOMY:
//!     the third option is the one round 5 itself built for Vec-vs-Seq — READ
//!     THE ORIGIN SPELLING — and `a43`/`a44` measure that the spec surface costs
//!     nothing to keep.
//!
//!     THE RULE, stated once, AS AMENDED BY ROUND 7. The ghost/spec skip is
//!     granted only on POSITIVE evidence, never on absence of exec evidence.
//!     Positive evidence is exactly: an origin SPELLING in the spec table
//!     (`Seq`/`Set`/`Map`/`Multiset`) recorded at a seam that actually saw it —
//!     the parameter-typing seam, and since round 7 the STRUCT-FIELD and
//!     TUPLE-COMPONENT seams as well; an element of a receiver already
//!     established ghost; a ghost CONSTRUCTOR result; a `.view()`/`to_seq`/
//!     `to_set` ghost view; a ghost combinator chain over any of those; a spec
//!     collection macro; or branches that ALL agree on one of those. Everything
//!     else is exec (checked, with the element sort minted) or unresolved
//!     (checked, fail closed).
//!
//!     ROUND 6 ALSO ADMITTED an UNBOUNDED MATHEMATICAL element sort
//!     (`int`/`nat`/`Real`) as positive evidence, on the ground that no exec
//!     container can hold one. That is RETIRED: `trust-vc-types` declares
//!     `pub type int = i128;` and `pub type nat = u128;`, so the ground was
//!     false and the reading was granting the skip to exec containers reached
//!     through a field, a tuple or an index (`y1`, `z1`-`z4`).
//!
//!     Nested collections are deliberately NOT positive evidence: a
//!     `Vec<Vec<u64>>` models as `Seq(Seq(Uint))`, and admitting "the element is
//!     itself a collection" would hand the skip to an ordinary exec `Vec` of
//!     `Vec`s (`p12` pins that boundary).
//!
//!     WHAT REMAINS OF ROUTE A, and why it is information rather than a disabled
//!     check: at a POSITIVELY GHOST sink position — the constructor
//!     `Seq::new(n, |i| 10u64 / i)` (`u1e`) and the ghost VIEW
//!     `v@.map(|x| x / 0u64)` (`u1k`) — the sink's own signature says the
//!     closure is a SPEC function, whose body never runs and carries no runtime
//!     panic obligation. The decisive pair still diverges there (`d5` pins that
//!     the bare literal IS checked), and that divergence is disclosed, not
//!     laundered: what separates it from the rebind blockers is that the sink
//!     supplies NEW information about ghostness, where a rebind supplied none.
//!     Requirement 2 mandates exactly this exception. Both are now VERDICT pins
//!     (round 6): the rule says why they verify, so agreement pins would be
//!     understating what is known.
//!
//!     ROUND 3'S CONSTRUCTOR OVERRIDE IS RETIRED, WITH COUNTER-EVIDENCE. It read
//!     a WRITTEN exec scalar parameter as "exec wherever it is handed", which is
//!     a claim about SPELLING, and the corpus's cardinal spec surface refutes it:
//!     `SpecFn::new(|i: usize| 10i32 * (i as i32))` is how the lib fixtures
//!     `vc_extraction::tests::seq_concrete_ext_eq::*` write a spec function, and
//!     the override turned both from GREEN AT THE MERGE BASE into a
//!     `Counterexample` over an arbitrary `i`. A THIRD over-rejection from the
//!     same override was found by running this suite after the retirement:
//!     `x1b` — `Seq::new(n, |i: u64| i + 1u64)` — was filed under the disclosed
//!     X1 arbitrary-parameter class, but the receiver is a SPEC constructor, so
//!     it is not that class at all; it is re-keyed to `a46` and verifies, as it
//!     did at the merge base. `e24`/`e25` are re-keyed to `a40`/`a41` (same
//!     bodies, opposite verdict) and the protective content of the override — a
//!     closure that ALSO escapes or is called — is pinned where it actually
//!     lives, in `ClosureUseScan` (`e24c`/`e24d`).
//!   * ROUTE D (round 6, DISCLOSED, sound). `for_each` and `retain` are NOT in
//!     `pure_ghost_collection_combinator`, so an untyped closure handed to one
//!     of them is CHECKED but never reaches the mint — its verdict is an
//!     `Error`/`unresolved variable` rather than a counterexample. That is a
//!     capability gap on the reporting side, never a skip: both are already in
//!     the round-5 decisive-pair table as non-weakening.
//!   * ROUTE C. A closure literal inside `vec![..]` (`w1`). The collector
//!     visits each `vec!` element (parsed from the macro's tokens) and checks
//!     its arithmetic (`w1d`), and each element is planned like the function
//!     body before that visit, so the literal is checked at its definition and
//!     refuted. The plan uses the loop depth of the element (`w1g`/`w1h`) and
//!     the function's `let` receiver sorts (`w1i`). `w1b`'s constant zero
//!     divisor is an encoder refusal inside and outside a macro. Other macro
//!     token streams are still opaque to both. The NAMED spelling is pinned
//!     too (`w2`).
//!
//! No residual is pinned green: asserting its current verdict would cement a
//! false-`Verified`. What IS pinned is that each skip is INDISCRIMINATE — the
//! liar and an honest structural twin get the SAME verdict, because the rule
//! looks at neither body. A fix that closes a residual makes them diverge and
//! fires the pin, which is the signal to re-key it. Round 3 left all six repros
//! in PROSE ONLY, so nothing in the tree could have surfaced a change in their
//! status in either direction.
//!
//! ROUND 4 closed the LAST spelling of "adding a use disables the check", the
//! over-rejection round 3b opened, and the one guard round 3 shipped with no
//! discriminating pin:
//!
//!   * `e27`/`e27b`/`e27c`/`e28`/`e29` / `a23`/`a23b`/`a25` — THE IN-LOOP
//!     DEFINE-AND-CALL, the third corner of the loop family (`e14` is defined
//!     outside/called inside, `e19` is defined inside/escapes). `ClosureUseScan`
//!     is BLOCK-LOCAL and was seeded at depth zero, so a binding inside a loop
//!     body had no syntactic evidence of the enclosing loop and its in-loop
//!     `g(a, 0)` was classified a COVERING call — while
//!     `maybe_emit_invoked_exec_closure_arith_safety` bails outright inside any
//!     loop context. Neither site emitted. `e27b` is the decisive pair: deleting
//!     the call counterexamples, i.e. ADDING A USE made an unchecked closure
//!     LESS checked. `ClosureDefSitePlanner` now carries the enclosing
//!     loop/closure depth through its walk and seeds the scan with it, and the
//!     planner's OTHER skip — the immediately-invoked literal, which defers to
//!     the same lane — is gated on the same depths (`e28`). The seeding gates
//!     the COVERING-CALL classification ONLY, which `a27` measures: a ghost
//!     argument defers to no lane, so gating it too pushed a spec closure bound
//!     inside a loop into an `Incompleteness` over its ghost body. `a28` is the
//!     nested-closure control.
//!   * `a24`/`e30` — THE OVER-REJECTION ROUND 3b OPENED. The sibling-arm
//!     suppression (`e26`) kept the scan walking past an arm's write so the
//!     SIBLING arm is still seen, but it also kept charging uses that come AFTER
//!     an arm's own unconditional write to the original literal, which is dead
//!     from that point on that path. `a24` verified at the merge base and was
//!     rejected here — and not through the `x1` class: both live bodies divide
//!     by a nonzero constant. The kill is now ARM-LOCAL
//!     (`ClosureUseScan::arm_dead`), reset at every arm boundary. `e30` is the
//!     liar twin that proves it only MOVES the obligation to the literal that
//!     actually escapes.
//!   * `e31`/`a26` — the `closure_is_call_site_instrumentable` early return in
//!     `closure_uses_are_covered` shipped in round 3 with no named
//!     discriminator. It has one now: a body that re-binds a parameter name
//!     makes the call-site lane bail, so a direct call on it is not coverage.
//!
//! ROUND-4 NEUTRALIZATIONS, each measured by disabling ONE guard:
//!   * the planner's depth carrying -> the scan seeded at 0 again: exactly
//!     `e27`, `e27c`, `e29`.
//!   * the immediately-invoked literal's depth gate -> removed: exactly `e28`.
//!   * `ClosureUseScan::arm_dead` -> never set (round-3b behaviour): exactly
//!     `a24`.
//!   * `closure_is_call_site_instrumentable` in `closure_uses_are_covered` ->
//!     removed: exactly `e31`.
//!
//! ROUND 5 CLOSED ROUTE A ON THE EXEC SIDE — the last
//! ADDING-A-USE-DISABLES-THE-CHECK route this suite knew about, and the one the
//! branch's own disclosure UNDERSTATED (see the corrected ROUTE A entry above):
//!
//!   * `u1`/`u1c` RE-KEYED from agreement pins to verdict pins, plus
//!     `n1`-`n8` / `a29`-`a39` / `d`. The ghost-sink skip now reads the
//!     RECEIVER: `SinkReceiverEnv::classify` resolves a receiver to `Ghost`,
//!     `Exec(element sort)` or `Unresolved` from `VariableDecl::bounded_len`
//!     (function parameters), a `let` annotation or initializer (locals), a
//!     ghost constructor call, a `.view()`, or a combinator chain over any of
//!     those. Only `Ghost` skips. `Exec` is CHECKED with the element sort minted
//!     for the closure's UNWRITTEN parameters — which is what makes the probe a
//!     REFUTATION rather than the `Error` round 3 measured (`n2`, and `n1` for
//!     the named spelling, whose receiver is reached through `ClosureUseScan`).
//!     `Unresolved` is CHECKED too: FAIL CLOSED (`n7`), because an unresolvable
//!     receiver is exactly where a wrong guess is dangerous.
//!   * `d` is THE BAR, executable: every exec-sink shape against the IDENTICAL
//!     body with the sink DELETED (`assert_sink_does_not_weaken`), the same
//!     comparison `e27`/`e27b` make for the loop case.
//!   * `n8` pins the one piece of inference that is NOT the element sort: a
//!     FOLD's accumulator takes its sort from the INITIAL VALUE. Both mintings
//!     refute, so only the reported model can see it — and a counterexample
//!     naming a `u64` for a `u32` program variable misdescribes the program.
//!
//! ROUND-5 NEUTRALIZATIONS, each measured by disabling ONE guard and running the
//! whole suite:
//!   * the receiver rule -> round-4 behaviour (skip whenever the parameter list
//!     is not fully written exec scalars): `u1`, `u1c`, `n1`, `n2`, `n2b`, `n3`,
//!     `n4`, `n5`, `n6`, `n7`, `n8`, `n9`, `x2`, `d` (14). CORRECTED IN ROUND 6:
//!     round 5 published 12 and omitted `n8`/`n9`, which the reviewer measured
//!     red as well. Every claimed partition below was a SUBSET of the measured
//!     one; the counts are the measured ones.
//!   * the FAIL-CLOSED half alone (`Unresolved` treated as ghost, i.e. only a
//!     resolved `Exec` checked): `n7`, `n9`, `x2`, `d` (4) — round 5 published 3
//!     and omitted `n9`.
//!   * the parameter-sort inference at the mint: `n1`, `n1b`, `n2`, `n2b`,
//!     `n3b`, `n4b`, `n5b`, `n6b`, `n8`, `n8b`, `u1`, `x2c` (12) — round 5
//!     published 10 and omitted `n8`/`n8b`. Round 3's measured objection,
//!     reproduced: without it the fix costs capability broadly.
//!   * the NAMED-spelling inference (carried back from `ClosureUseScan` to the
//!     binding): exactly `n1`, `n1b` (2).
//!   * the FOLD accumulator split: exactly `n8` (1).
//!   * the SHADOW disagreement rule (let a later `let` that shadows a function
//!     parameter win): exactly `n9` (1) — and it goes red with a
//!     false-`Verified`, because the earlier exec `.map` would inherit the ghost
//!     shadow's skip.
//!
//! ROUND 6 CLOSED THE THREE THINGS ROUND 5 LEFT: the exec side of route A in
//! the `Set`/`Map` containers (blocker), the two lib tests the branch itself
//! turned red (blocker), and the ghost-surface half of the fail-closed cost
//! (over-rejection). Its pins are `p1`-`p15b`, `a40`-`a45`, `d6`, `x3`, plus the
//! four RE-KEYS requirement 4 demands (`u1e`, `u1k`, `x2`, `e24`/`e25`).
//!
//! ROUND-6 NEUTRALIZATIONS, each measured by disabling ONE guard and running the
//! WHOLE suite (five runs, 1242-1395 s each, load 8-29). Every one is 105
//! passed / 2 failed: no guard is undiscriminated, and no guard reds anything
//! outside its own partition — no collateral, and no load flake in any of the
//! five.
//!   * the EXEC-CONTAINER origin table off (`syn_type_string_is_exec_std_container`
//!     always `false`, i.e. round 5's reading of `Set`/`Map`): exactly
//!     `p1_p6_an_exec_std_set_or_map_is_checked` and
//!     `p1b_p6b_the_honest_exec_set_map_twins_still_verify` — BOTH directions,
//!     because without the exec reading there is no mint either.
//!   * ROUND 3'S CONSTRUCTOR OVERRIDE restored (`ghost_closure_sink_call &&
//!     !closure_params_are_written_exec_scalars`): exactly
//!     `a40_a42_a_ghost_constructor_is_a_ghost_receiver` and
//!     `x1_unguarded_arithmetic_on_a_fresh_parameter_is_rejected` (which carries
//!     `a46`). That partition IS the blocker: those two tests are the three
//!     over-rejections the override caused.
//!   * the POSITIVELY-GHOST ELEMENT SORT off (`positively_ghost_element_sort`
//!     always `false`): exactly `p7_p14_unresolvable_ghost_receivers_are_recovered`
//!     and `p10_the_map_index_receiver_is_not_what_is_rejected`.
//!   * the BRANCH-ARM JOIN off (`if`/`match`/block tail -> `Unresolved`):
//!     exactly `p7_p14_unresolvable_ghost_receivers_are_recovered` and
//!     `x2_the_unresolvable_receiver_cost_is_now_the_chained_receiver_only`.
//!   * the NESTED-COLLECTION EXCLUSION removed (admit `Seq`/`Set`/`Map`/
//!     `Multiset` as ghost element evidence): exactly
//!     `p11_p15b_the_exec_half_of_the_same_two_readings_stays_checked` and
//!     `d6_adding_an_exec_set_or_map_sink_never_removes_an_obligation` — and it
//!     goes red with a false-`Verified`, which is why the exclusion is stated in
//!     `positively_ghost_element_sort`'s doc as a soundness boundary.
//!
//! LOAD NOTE for every one of those counts: the loop-shaped pins `a9`, `a14`,
//! `a23`/`a23b` — and, measured for the first time in round 5, `a21` — belong to
//! the documented load-sensitive class (see `a9`) and are excluded from the
//! partitions above. They were red in the UN-neutralized run at the same load
//! and `a9` was red at the PRE-CHANGE engine under the same load with identical
//! `Unknown` text, which is the attribution; all four were green run alone once
//! the load average fell to ~12.
//!
//! THE TWO RED LIB TESTS WERE THE BRANCH'S OWN, AND ROUND 6 FIXED THEM.
//! Round 5 ran `targo --unverified test -p trust-vc-core --lib` — 17221 passed,
//! 2 failed — which earlier rounds had not: they measured the integration suites
//! only. Both failures are
//! `vc_extraction::tests::seq_concrete_ext_eq::{concrete_generator_vs_push_chain_speceq_verifies,
//! auto_extensionality_syntax2_port_verifies}`, reached through
//! `SpecFn::new(|i: usize| 10i32 * (i as i32))`.
//!
//! ROUND 5 MISATTRIBUTED THEM. It called them PRE-EXISTING and said it had
//! measured them "at both revisions" — but both revisions it measured were
//! INSIDE the branch. Measured against the MERGE BASE (`31493465`) they are a
//! BRANCH REGRESSION: 11/11 green at the base and at the round-2 tip, 2 FAILED
//! from the round-3 tip onward. They were introduced by round 3's
//! constructor-sink override, and rounds 3 and 4 shipped without running the lib
//! tests at all.
//!
//! Round 5 then declined to fix them on the ground that narrowing the override
//! "relaxes a soundness override that ships with its own pins". Round 6 does not
//! narrow it for `SpecFn` alone — it RETIRES it, because the reading it
//! implements (a parameter's SPELLING decides whether a spec function's body is
//! exec) is the same reading this campaign already removed from the combinator
//! rule, and the cardinal spec surface is its counter-example. `-p
//! trust-vc-core --lib -- seq_concrete_ext_eq` is 11/11 green again, and `a42`
//! pins the same shape from the integration suite so it cannot go red unnoticed
//! a third time.
//!
//! MEASURED AT ROUND 6, cache off, `targo --unverified`, load ~7:
//!   `-p trust-vc-core --lib`                17225 passed / 0 failed (662 s)
//!   `--test closure_escape_body_soundness`    107 passed / 0 failed (1213 s)
//!   `--test be_frame_round8_soundness`         20 passed / 0 failed (0.29 s)
//! Earlier round-6 lib runs at load ~15 and ~10 reported 4 and then 1 failure;
//! each of those tests passes ALONE (3/3, 25.5-34 s) and the union of them is
//! four tests, none in the changed lane. They are the documented LOAD-SENSITIVE
//! class, and the load-~7 run above is 17225/0 — recorded as an ATTRIBUTION,
//! not a dismissal, because round 5 got exactly this wrong by measuring only
//! inside the branch.
//!
//! ROUND 6b (THE ROUND-6 ADVERSARIAL REVIEW) FOUND ONE MORE
//! ADDING-A-USE-DISABLES-THE-CHECK ROUTE AND CLOSED IT, plus one residual whose
//! JUSTIFICATION was false.
//!
//!   * `m1`-`m7` — THE MINT'S WIDTH. Round 5 gave a checked literal's UNWRITTEN
//!     parameters the element sort of the FIRST exec receiver the NAME is
//!     applied to, and said in-code that a wrong width "can only be observed in
//!     the reported model … never by discharging an obligation the true width
//!     would refute". Measured on the round-6 tip, that is refuted:
//!     `let g = |x| if x < 100 { x * 3 } else { 0 };` applied to a `Vec<u64>`
//!     and THEN to a `Vec<u8>` published `Verified`, while the same body with
//!     the `Vec<u64>` use DELETED counterexamples on the genuine `u8` overflow.
//!     One definition-site frame serves EVERY application, so the borrowed width
//!     discharged an obligation at a receiver it did not come from. The same
//!     false verify was measured with the second receiver UNRESOLVED (`m3`,
//!     `w.to_vec()`). EVERY checked use is now joined pairwise and a
//!     disagreement — an unresolved receiver included — drops that position's
//!     mint and fails closed. A GHOST use contributes nothing and may not veto a
//!     mint (`m7`), because a spec application carries no runtime obligation.
//!     `m2`/`m4`/`m5` are the over-rejection controls and `m6` is the disclosed
//!     cost: an HONEST body at a resolved receiver plus an unresolved one no
//!     longer borrows the resolved width.
//!   * `y1`/`y2` — A MATHEMATICAL ELEMENT SORT IS A SPELLING, NOT A PROOF.
//!     Round 6 justified `positively_ghost_element_sort` as "no exec Rust
//!     container can hold `int`/`nat`/`Real`". `trust-vc-types` declares
//!     `pub type int = i128;` and `pub type nat = u128;`, so `Vec<int>` is a
//!     constructible exec container; the PARAMETER seam reads that spelling as
//!     `CollectionOrigin::Exec` and CHECKS the closure (`y2`), while the same
//!     type behind a FIELD kept the ghost skip (`y1`) with a decisive pair
//!     against its no-sink twin (`y1c`). Held as an AGREEMENT pin and disclosed
//!     — and CLOSED IN ROUND 7, which is why those pins are now real verdicts.
//!
//! ROUND 7: FIELD-LEVEL COLLECTION PROVENANCE. One missing capability caused
//! BOTH of round 6b's open items, so one change closes both.
//!
//!   * THE FALSE VERIFY (`y1`, `z1`-`z4`). The retired element-sort reading was
//!     the only ghost evidence a field/tuple/index receiver could produce, and
//!     it was false. Retired OUTRIGHT rather than narrowed: its entire content
//!     was the premise "this element sort cannot occur in an exec container",
//!     and the premise is untrue of `int` and `nat` here — resting the rule on
//!     `Real` alone would be the same argument one type-alias away from failing
//!     again. Measured route by route: a `Vec<nat>` field, a `BTreeSet<int>`
//!     field, a `(Vec<int>, u64)` tuple component, and a `Vec<Vec<int>>` INDEX
//!     (the route round 6b named but never fixtured) were all `Verified` with a
//!     liar body before, and all fail closed after.
//!   * THE OVER-REJECTION (`x3`, and the tuple twin `z3b`). A struct FIELD's
//!     origin spelling reached NOTHING — `StructDef` records modeled field types
//!     only — so a genuine spec `Seq<u64>` field was indistinguishable from a
//!     `Vec<u64>` field and failed CLOSED. Round 7 records the field's own
//!     spelling at the source-struct seam and the tuple component's at the
//!     binding seam, so `x3` VERIFIES while `x3b` — the same body at the same
//!     element width behind a `Vec<u64>` field — REFUTES. That pair is the liar
//!     twin of the recovery, and it is what shows the recovery is provenance and
//!     not "fields are ghost".
//!   * THE DESIGN DECISIONS ROUND 6 MADE FOR THE PARAMETER SEAM, restated and
//!     both still applying. (1) SIDE TABLES, not fields on `StructDef`/
//!     `VariableDecl`: a missing entry and `CollectionOrigin::Unknown` mean the
//!     same fail-closed thing, so the hundreds of construction sites outside the
//!     seam keep meaning what they meant and none can assert a provenance it
//!     never measured. (2) IN THE QUERY KEY: a context in which a field's
//!     provenance has not been recorded produces FEWER obligations than the same
//!     context with it, and two such contexts must never share a cache entry.
//!     ONE decision is NEW and it is a soundness point: the tuple table is keyed
//!     by the BINDING, not by the carrier, because a tuple's carrier NAME is
//!     built from its MODELED element types, so `(Vec<u64>, u64)` and
//!     `(Seq<u64>, u64)` name the SAME carrier — `z3b`/`z3c` are that pair.
//!   * WHAT STAYS FAIL-CLOSED, pinned rather than left to be found: a field
//!     spelled through a TYPE ALIAS (`z5`), a tuple nested BELOW the root
//!     binding, an enum carrier (registered as a type alias, so no entries), and
//!     a generic carrier whose monomorphised name is not the template name. All
//!     four read `Unknown` and CHECK the body.
//!
//! ROUND-6b NEUTRALIZATIONS. The new guard AND all five of round 6's were
//! re-measured over the WHOLE suite at 113 tests, six runs, 1280-1583 s each at
//! load 9-22. Every one reds ONLY named tests; there is no collateral and no
//! load flake in any of the six, and `git status`/`git diff` are empty after
//! each restore-by-copy.
//!   * the mint AGREEMENT rule -> round-5 FIRST-USE-WINS (G12, new): 111/2,
//!     exactly `m1_m3_a_second_receiver_may_not_reuse_the_first_ones_width`
//!     (which goes red with the FALSE `Verified`) and
//!     `m6_the_disclosed_cost_of_refusing_a_borrowed_width` (which goes red
//!     from the other side — the disclosed cost disappears, so the pin measures
//!     the price as well as the fix).
//!   * the exec-container origin table off (G7): 111/2, `p1_p6…`, `p1b_p6b…`.
//!   * round 3's constructor override restored (G8): 111/2, `a40_a42…`, `x1…`.
//!   * the positively-ghost element sort off (G9): 110/3, `p7_p14…`, `p10…`,
//!     and — new this round — `y1_y2…`, which is the reading `y1` pins.
//!   * the branch-arm join off (G10): 111/2, `p7_p14…`, `x2…`.
//!   * the nested-collection exclusion removed (G11): 111/2, `d6…`,
//!     `p11_p15b…`.
//!
//!   Round 6's own five counts are reproduced exactly (its 105/2 is 111/2 here
//!   only because this round added six tests).
//!
//! ROUND-7 NEUTRALIZATIONS. Five runs over the WHOLE suite at 118 tests,
//! 1255-1525 s each at load 10-18, cache off, each restored by copy with
//! `git status`/`git diff` empty afterwards. The un-neutralized baseline is
//! 118/0 in 1271 s.
//!   * the RETIRED element-sort reading RESTORED (G13, new): 117/1, exactly
//!     `z5b_z5c_what_retiring_the_element_sort_reading_costs` — and it reds with
//!     a FALSE `Verified` (`z5b_alias_ghost_field_over_rejection` verifies
//!     again). That partition is the attribution for the disclosed cost AND the
//!     proof that the reading was granting the skip on a spelling nobody
//!     measured. It reds NOTHING else, which is the measurement that says the
//!     `p7`-`p14` ghost surface is recovered by PROVENANCE and not by the
//!     reading.
//!   * the STRUCT-FIELD provenance table off (G14, new): 113/5, exactly
//!     `p7_p14…` (`p7`), `x3…`, `z5b_z5c…` (through its `p7` narrowing
//!     control), `z6…` (the field mint disappears, so `z6b` degrades from a
//!     refutation to an incompleteness) and `z7…` (`z7b`). Every one is an
//!     OVER-REJECTION: a table that only ever turns `Unresolved` into a
//!     measured reading cannot red a soundness pin, and it does not.
//!   * the TUPLE-COMPONENT provenance table off (G15, new): 116/2, exactly
//!     `p7_p14…` (`p8`) and `z3b_z3c…`.
//!   * the INDEX route's base classification off — round 6's hard-coded
//!     `Unknown` (G16, new): 117/1, exactly
//!     `p10_the_map_index_receiver_is_not_what_is_rejected`.
//!   * THE ROUND-6 CONFIGURATION in full — the reading restored AND both tables
//!     off (G17, new, and deliberately a TWO-GUARD neutralization): 112/6,
//!     exactly the six round-7 tests `x3…`, `y1_y2…`, `z1_z5…`, `z3b_z3c…`,
//!     `z5b_z5c…`, `z6…`, with the FALSE VERIFIES back on `y1`, `z1` and `z5b`.
//!     This is the only neutralization that re-opens the hole, and that is a
//!     FACT ABOUT THE PINS worth stating plainly: neither half alone re-opens
//!     it, because with the reading retired an unmeasured field fails CLOSED and
//!     with provenance recorded the reading never gets consulted. So `y1` and
//!     `z1`-`z4` are discriminated by the COMBINED configuration and by no
//!     single guard — recorded as such rather than claimed as single-guard
//!     discriminated.
//!
//!   `z7…` is the one round-7 test G17 does NOT red, which is right: under
//!   round 6's reading a nested `Seq<int>` field was ghost for the wrong reason
//!   and its exec twin still failed closed.
//!
//! ROUND-7 REVIEW found the SIXTH "adding something disables the check" route,
//! and it is one round 7 itself opened. Round 7 records collection provenance
//! against the DECLARED binding — the field table keyed by the carrier
//! `get_variable_type` answers with, the tuple table keyed by the binding NAME —
//! while the sink scan is FLAT over the whole body, and nothing re-resolved the
//! ROOT of a field projection. The `Expr::Path` route has carried a shadow rule
//! since round 5; the `Expr::Field` route round 7 re-keyed did not get one.
//! Measured at `7119a236`, cache off, all five `Verified` on bodies that ALWAYS
//! divide by zero: `zzs1` (a parameter `t: (Seq<u64>, u64)` rebound by
//! `let t = (w, 1u64)` over an exec `w: Vec<u64>`), `zzs2` (the same with an
//! EXPLICIT `let t: (Vec<u64>, u64)` annotation, so the hole is the root and not
//! the initializer classifier), `zzs3` (the STRUCT-carrier twin, which is what
//! says both tables are affected and not just the tuple table's binding key),
//! `zzs4` (the rebind in an inner block) and `zzs4b` (a 3-tuple at index 1).
//! `zzs1b`/`zzs1c` are the decisive controls: RENAMING or DELETING the shadowed
//! parameter left the identical body a non-verify, so the skip was bought by the
//! NAME of an otherwise unused parameter. The guard fails closed on a let-bound
//! root, and `zzs7`/`zzs8` measure what that costs: nothing — a purely local
//! carrier resolved no field provenance before the guard either.
//!   * the shadow guard removed (G18, new): 121/1, exactly `zzs1_zzs4…` and
//!     nothing else, and it reds with a FALSE VERIFY on `zzs1`. The decisive
//!     controls `zzs1b`/`zzs1c` stay GREEN under it, which is what says the
//!     guard discriminates the SHADOW and not the body, and `zzs5`-`zzs8` stay
//!     green, which is what says it is not a blanket refusal.
//!
//! ROUND-7 REVIEW ALSO RE-RAN ROUND 7's OWN FIVE, each over the WHOLE suite,
//! restore-by-copy, `git diff` empty after every one. All five partitions
//! reproduce; the counts differ from round 7's only by the tests this review
//! added (`zzs*`, `v1_v4`):
//!   G13 120/2 (`z5b_z5c`, `v1_v4` — both FALSE-VERIFY; round 7 saw 117/1 and
//!       the second red is exactly the disclosure this review corrected)
//!   G14 115/7 — ZERO false verifies (6 `OVER-REJECTION` panics plus `z6b`
//!       "expected a refutation, got an incompleteness"), so round 7's claim
//!       that the field table can only ever turn `Unresolved` into a MEASURED
//!       reading holds as measured and not as prose
//!   G15 119/3 · G16 121/1 (`p10` only) · G17 114/8 with FOUR false verifies
//! THE TWO-GUARD DISCLOSURE IS ACCURATE, and this is the measurement that
//! settles it: G14 and G15 each red ZERO false verifies alone, G13 alone reds
//! only the two disclosure tests, and only the COMBINATION puts `y1`, `z1`,
//! `z5b` and `v1` back to `Verified`.
//!
//! ROUND-7 REVIEW also CORRECTED a round-7 disclosure rather than inheriting it:
//! the TYPE ALIAS is not "the ONLY thing the retirement costs" — see
//! `v1_v4_the_retirement_costs_more_than_the_alias`, four more spec receivers
//! round 6's reading recovered and round 7 does not, one of which (`v4`) is a
//! FIELD and so refutes the wording directly.
//!
//! ROUND 8 reviewed the round-7 review's own fix and found the SEVENTH "adding
//! something disables the check" route — this time in the map BOTH shadow rules
//! read. `LetBindingCollector` recorded a binding only when
//! `local_ident(&local.pat)` answered, i.e. only for a `let` whose pattern is a
//! PLAIN IDENT, so a destructuring `let`, a struct-pattern `let`, a `match` arm,
//! a closure parameter and a `for` pattern all rebound a name INVISIBLY and the
//! function PARAMETER of that name kept answering. Nine shapes, all `Verified`
//! at `aeb1f4c0` on bodies that always divide by zero (`zt1`-`zt9`), with the
//! renamed/deleted-parameter controls (`zt1b`/`zt1c`) non-verifies at the same
//! commit. FIVE of the nine are on the `Expr::Path` route, so this was ROUND 5's
//! blind spot for three rounds and not only round 7's.
//!
//! The round-8 guard is the FIRST in this campaign whose cost is not nothing,
//! and it is recorded as such: the binder set is FLAT, so a closure parameter or
//! a `for` binding that happens to share the RECEIVER's name now fails closed
//! (`zt17`/`zt18` — `s.map(|s| s + 1)` verified before and does not now). That
//! is the acceptable direction of the trade; scoping the map is what would buy
//! it back.
//!
//!   G19 the round-8 opaque-binder recording removed   124/2, and ONLY the two
//!       round-8 tests: `zt1_zt9…` reds with a FALSE VERIFY on `zt1`, and
//!       `zt17_zt18…` reds — which is what attributes the disclosed cost to this
//!       guard rather than to something else. `zt14_zt16…` (the liar twin) and
//!       `zt10_zt13…` stay GREEN under it, so it is not a blanket refusal.
//!
//! ROUND-10 REVIEW RE-RAN ROUND 7's FIVE AND ROUND 8's ONE, which round 9
//! skipped for budget. Each over the WHOLE suite, in a SEPARATE detached
//! worktree at `5106f577` so the sweep measured the guards at exactly the
//! commit under review; restore-by-copy, source md5-identical and
//! `git status --short` empty after every one. Baseline there: 130/0 in 1376 s.
//!   G13 127/3, 1854 s — `z5b_z5c` and `v1_v4`, BOTH with false verifies
//!       (`z5b_alias_ghost_field_over_rejection`,
//!       `v1_generic_carrier_spec_seq_field_over_rejection`), i.e. round 8's
//!       partition exactly. The third red,
//!       `a23b_honest_immediately_invoked_literal_inside_a_loop_verifies`, is
//!       an OVER-REJECTION caused by a 60 s BV solver TIMEOUT (#1605) under the
//!       concurrent round-10 validation run — LOAD, not a partition member.
//!   G14 121/9, 1450 s — ZERO false verifies; every red is an over-rejection or
//!       an "EXPECTED A REFUTATION" incompleteness.
//!   G15 125/5, 1355 s — ZERO false verifies, same character.
//!   G16 129/1, 1393 s — EXACTLY `p10`, and it reds as a `RESIDUAL MOVED`
//!       agreement pin rather than as a false verify.
//!   G17 120/10, 1272 s — FOUR false verifies, and exactly the four round 8
//!       named: `y1`, `z1`, `z5b`, `v1`.
//!   G19 128/2, 1294 s — EXACTLY `zt1_zt9` (false verify on `zt1`) and
//!       `zt17_zt18` (the disclosed cost disappears, which ATTRIBUTES it).
//!       `zt10_zt13` and `zt14_zt16` stay GREEN.
//! In every case the count differs from round 8's only by the tests added
//! since. ROUND 7's TWO-GUARD DISCLOSURE THEREFORE STILL HOLDS UNDER A FRESH
//! MEASUREMENT, and this is what settles it: G14 and G15 each red ZERO false
//! verifies alone, G13 alone reds only the two disclosure tests, and ONLY the
//! combined round-6 configuration (G17) puts `y1`, `z1`, `z5b` and `v1` back to
//! `Verified`.
//!
//! ROUND 10's own guard, neutralized over this suite: the spec-NAME scope rule
//! removed (G23) leaves it 130/0 — NO collateral, because no fixture here
//! redefines a spec-collection name. Its partition lives in
//! `spec_name_scope_soundness`.
//!
//! CACHE DISCIPLINE (mandatory): the on-disk verification cache stores only
//! `Verified` results and survives `cargo clean`, so every verdict here is
//! recomputed with `TRUST_VC_DISABLE_VC_CACHE=1`. Round 4 extended the same
//! discipline to `be_frame_round8_soundness`, whose `run` helper called
//! `verify_function_from_file` directly and so inherited whatever the caller's
//! environment happened to be — measured, it costs that suite nothing (20 tests
//! in 0.45 s with the cache off), so its speed was never evidence of
//! cache-serving.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/closure_escape_body_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&repro_path(), func)
    })
}

fn verdict(func: &str) -> VerifyResult {
    verify(func).unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

/// Pin that two fixtures get the SAME KIND of verdict, without saying which.
///
/// This is how a DISCLOSED RESIDUAL is kept executable without cementing its
/// current (false-`Verified`) answer: the residual and an honest structural twin
/// are pinned to agree, because the rule that skips them looks at neither body.
/// A fix that closes the residual makes them diverge and fires this pin, which
/// is the signal to re-key it.
fn assert_same_verdict(residual: &str, control: &str) {
    let (a, b) = (verdict(residual), verdict(control));
    assert_eq!(
        std::mem::discriminant(&a),
        std::mem::discriminant(&b),
        "RESIDUAL MOVED: `{residual}` -> {a:?} but its control `{control}` -> {b:?}. \
         This pin asserts only that the skip is INDISCRIMINATE; a divergence means \
         the residual's status changed and the suite header must be re-keyed."
    );
}

/// An extraction `Err` and any solver non-`Verified` (including `Unknown`) are
/// sound non-verifies; only `Verified` is the false-verify.
fn assert_not_verified(func: &str) {
    if let Ok(VerifyResult::Verified) = verify(func) {
        panic!("ESCAPING-CLOSURE FALSE-VERIFY: `{func}` must not verify")
    }
}

/// Acceptance: exactly `Counterexample`. Stronger than `assert_not_verified`,
/// and the ONLY thing that discriminates the round-5 parameter-sort INFERENCE:
/// without it the same probe fails closed into an `unresolved variable`
/// incompleteness, which `assert_not_verified` would happily accept.
fn assert_counterexample(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "EXPECTED A REFUTATION: `{func}` must come back a counterexample \
         (a non-verify that is merely an incompleteness means the closure's \
         parameter sort was not inferred from its receiver); got {v:?}"
    );
}

/// THE DECISIVE-PAIR BAR (round 5). `with_sink` and `without_sink` are the SAME
/// closure body, one handed to a higher-order sink and one not. Adding a use may
/// never remove an obligation, so a body that is checked WITHOUT the sink must
/// still be checked WITH it. Only the one distinction that matters is compared:
/// the sink may not turn a non-verify into a `Verified`.
fn assert_sink_does_not_weaken(with_sink: &str, without_sink: &str) {
    let bare = verdict(without_sink);
    if matches!(bare, VerifyResult::Verified) {
        // Nothing to preserve: the body carries no obligation on either side.
        return;
    }
    let sunk = verdict(with_sink);
    assert!(
        !matches!(sunk, VerifyResult::Verified),
        "SINK DISABLED THE CHECK: `{without_sink}` -> {bare:?}, but the identical \
         body handed to a sink made `{with_sink}` -> Verified. A check that can \
         be disabled by ADDING A USE is not a check."
    );
}

/// Acceptance: exactly `Verified`. An `Unknown` or an `Error` is a FAILURE — it
/// is capability loss wearing the costume of a soundness fix.
fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "OVER-REJECTION: `{func}` must verify; got {v:?}"
    );
}

// ── the control: the already-correct direct-call path ───────────────────────

#[test]
fn e0_direct_call_stays_closed() {
    assert_not_verified("e0_direct_call_cx");
}

// ── the escape routes, one test per route ───────────────────────────────────

#[test]
fn e1_higher_order_argument() {
    assert_not_verified("e1_higher_order_arg_cx");
}

#[test]
fn e2_inline_argument_literal() {
    assert_not_verified("e2_inline_arg_literal_cx");
}

#[test]
fn e3_stored_in_struct_field() {
    assert_not_verified("e3_struct_field_cx");
}

#[test]
fn e4_stored_in_tuple() {
    assert_not_verified("e4_tuple_cx");
}

#[test]
fn e5_returned_from_function() {
    assert_not_verified("e5_returned_cx");
}

#[test]
fn e6_shadowed_before_any_call() {
    assert_not_verified("e6_shadowed_cx");
}

#[test]
fn e7_captured_by_another_closure() {
    assert_not_verified("e7_captured_by_closure_cx");
}

#[test]
fn e8_never_called_at_all() {
    assert_not_verified("e8_never_called_cx");
}

#[test]
fn e9_anonymous_statement_literal() {
    assert_not_verified("e9_statement_literal_cx");
}

// ── the frame: parameters are FRESH, captures are the definition-site values ─

#[test]
fn e10_escaping_parameter_divisor_counterexamples() {
    // Mutation-sensitive: the verdict must be a COUNTEREXAMPLE, not merely a
    // non-verify. That is only reachable if the definition-site check declares
    // each parameter as a fresh symbol of its written sort — without the
    // declaration the obligation cannot lower at all and the verdict degrades to
    // an `unresolved variable` Error.
    let v = verdict("e10_escaping_symbolic_divisor_cx");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "an escaping closure dividing by its own PARAMETER should counterexample \
         over the fresh frame; got {v:?}"
    );
}

#[test]
fn a5_escaping_literal_divisor_verifies() {
    assert_verified("a5_escaping_literal_divisor_ok");
}

#[test]
fn e11_definition_site_path_condition_is_used() {
    // Defined under `if d == 0`: the body obligation is discharged under the
    // path condition that reaches the DEFINITION, so it fails.
    assert_not_verified("e11_definition_path_condition_cx");
}

#[test]
fn a7_definition_site_path_condition_discharges() {
    // The same closure under `if d != 0` must still verify — the twin that a
    // blanket "reject every escaping closure" fix would fail.
    assert_verified("a7_definition_path_condition_ok");
}

#[test]
fn e12_enclosing_fact_must_not_reach_a_shadowing_parameter() {
    // `requires(x != 0)` is about the FUNCTION's `x`. The closure's own `x` is a
    // parameter, arbitrary. A `Verified` here means a parent fact leaked INTO
    // the closure frame.
    assert_not_verified("e12_outer_fact_must_not_reach_param_cx");
}

#[test]
fn a8_capture_fact_reaches_the_body() {
    // The other direction of the same frame: a GENUINE capture keeps its
    // enclosing fact, so the identical division verifies.
    assert_verified("a8_capture_fact_reaches_body_ok");
}

// ── over-rejection controls: honest closures must still verify ──────────────

#[test]
fn a1_honest_higher_order_argument_verifies() {
    assert_verified("a1_honest_higher_order_arg_ok");
}

#[test]
fn a2_honest_inline_argument_verifies() {
    assert_verified("a2_honest_inline_arg_ok");
}

#[test]
fn a3_honest_never_called_verifies() {
    assert_verified("a3_honest_never_called_ok");
}

#[test]
fn a4_direct_call_with_safe_argument_keeps_verifying() {
    // THE retained capability: `|x, y| x / y` is safe only because of the CALL
    // ARGUMENT `5`. The definition-site check must not fire for a closure whose
    // every use is a covering direct call, or this capability is lost.
    assert_verified("a4_direct_call_safe_arg_ok");
}

#[test]
fn a6_spec_closures_are_never_instrumented() {
    // The cardinal exec-vs-spec discrimination, in both spellings.
    assert_verified("a6_spec_closure_inline_ok");
    assert_verified("a6b_spec_closure_named_ok");
}

#[test]
fn e13_inner_block_shadow_is_not_coverage() {
    // The nested-rebinding bail in `ClosureUseScan::visit_pat_ident`: without it
    // the inner block's `g(a)` is miscounted as coverage for the OUTER closure.
    assert_not_verified("e13_inner_block_shadow_cx");
}

#[test]
fn e14_call_inside_a_loop_is_not_coverage() {
    // The call-site lane defers inside a loop body, so a call there covers
    // nothing.
    assert_not_verified("e14_called_only_in_loop_cx");
}

#[test]
fn a9_honest_loop_called_closure_verifies() {
    // Non-vacuity twin for `e14`: the identical loop shape with a total body.
    //
    // LOAD-SENSITIVE, and the class is already documented: this is the only pin
    // in the file whose goal is a LOOP INVARIANT, and ay answers
    // `Unknown { reason: "... ((incomplete self-check-rejected)) for
    // 'loop_invariant_1'" }` on a busy box. Measured 2026-09-16: red inside a
    // full concurrent sweep (load average > 30), green every time it was re-run
    // ALONE.
    //
    // ROUND 5 CORRECTS THAT SECOND HALF: "green when run alone" is NOT the
    // invariant. At load average 33-38 this pin is red run ALONE as well (5/5),
    // with the identical `Unknown` text — and it is red 2/2 at the PRE-CHANGE
    // engine (`body_extract.rs`/`builders.rs` restored from the branch tip)
    // under the same load, which is the attribution: the load, not the planner.
    // `a9_loop_called_honest_ok` has no combinator and no ghost sink at all, and
    // its closure parameter is a WRITTEN exec scalar, so round 5's receiver rule
    // cannot reach it. Re-run on an IDLE box before attributing a red here to
    // the closure planner — the planner decides this closure's fate before any
    // solver call.
    assert_verified("a9_loop_called_honest_ok");
}

// ── H7: the other direction of the frame — body facts must not leak OUT ─────

#[test]
fn h7_never_called_assume_false_counterexamples() {
    // On main this was fail-closed only because the VACUITY GUARD fired: the
    // closure's `assume!(false)` had become a parent hypothesis, so every parent
    // obligation was vacuous. With the body's hypotheses scoped to the body, the
    // parent's `assert!(a != a)` is an ordinary refutable goal again — so the
    // verdict must be a COUNTEREXAMPLE, not `Unknown { VacuousTruth }`.
    let v = verdict("h7_never_called_assume_false_cx");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "an `assume!(false)` in a NEVER-CALLED closure must not reach the parent \
         path condition; got {v:?}"
    );
}

#[test]
fn h7c_body_assume_does_not_discharge_a_parent_assert() {
    assert_not_verified("h7c_body_assume_does_not_reach_parent_cx");
}

#[test]
fn h7b_closure_own_assume_implies_its_own_assert() {
    // The honest twin: scoping the body's hypotheses must not destroy the
    // closure's OWN reasoning.
    assert_verified("h7b_closure_own_assume_implies_assert_ok");
}

#[test]
fn h7d_a_later_assume_does_not_discharge_an_earlier_body_assert() {
    assert_not_verified("h7d_later_assume_must_not_discharge_earlier_assert_cx");
}

#[test]
fn h7e_body_vacuity_does_not_escape_to_the_parent() {
    // A contradictory in-body `assume!` makes the BODY's own downstream
    // obligations vacuous (Verus parity), but the parent's FALSE goal is still
    // refuted — the vacuity does not escape.
    assert_not_verified("h7e_body_vacuity_does_not_escape_cx");
}

#[test]
fn h7f_body_vacuity_leaves_the_parent_provable() {
    // Non-vacuity twin for `h7e`: the same vacuous closure with a TRUE parent
    // goal must still verify.
    assert_verified("h7f_body_vacuity_leaves_parent_provable_ok");
}

// ── ROUND-2: the routes the first increment left open ───────────────────────
//
// NON-DISCRIMINATION, measured and recorded rather than claimed away: five of
// the first increment's pins (`e5`, `e7`, `h7c`, `h7d`, `h7e`) also pass at the
// merge base, so they assert nothing ABOUT this change — `e5`/`e7` were already
// fail-closed for unrelated reasons (return-value lowering; an `unresolved
// variable` incompleteness), and `h7c`/`h7d`/`h7e` survive the H7 guard's
// removal. They are kept as regression material, not as evidence.

#[test]
fn e15_ghost_sink_method_name_alone_is_not_ghost() {
    // `pure_ghost_collection_combinator` is a NAME list and the modeled type
    // cannot separate a ghost `Seq` from an exec `Vec`, so the name-only skip
    // hid every exec `.map`/`.filter`/`.fold` closure.
    assert_not_verified("e15_ghost_sink_method_inline_cx");
    assert_not_verified("e16_ghost_sink_method_named_cx");
}

#[test]
fn a10_honest_combinator_closure_verifies() {
    assert_verified("a10_ghost_sink_method_honest_ok");
}

#[test]
fn a11_spec_closure_on_a_combinator_is_still_never_instrumented() {
    assert_verified("a11_spec_closure_on_combinator_ok");
}

#[test]
fn e17_reentrant_capture_is_arbitrary_in_the_body() {
    // The definition-site check models EVERY application, not the first: this
    // `FnMut` zeroes its own divisor, so the second call divides by zero.
    assert_not_verified("e17_fnmut_second_application_cx");
}

#[test]
fn a12_honest_capture_mutating_closure_verifies() {
    assert_verified("a12_mutating_capture_honest_ok");
}

#[test]
fn e18_inline_literal_in_a_modeled_mutator_is_visited() {
    assert_not_verified("e18_inline_literal_pushed_cx");
}

#[test]
fn a13_honest_inline_literal_in_a_modeled_mutator_verifies() {
    assert_verified("a13_inline_literal_pushed_honest_ok");
}

#[test]
fn e19_closure_defined_inside_a_loop_is_checked() {
    assert_not_verified("e19_defined_inside_a_loop_cx");
}

#[test]
fn a14_honest_loop_defined_closure_verifies() {
    // LOAD-SENSITIVE, same documented class as `a9` — re-run ALONE before
    // attributing a red here to the definition-site emitter.
    assert_verified("a14_loop_defined_honest_ok");
}

#[test]
fn h7g_an_in_body_assume_only_discharges_what_it_dominates() {
    assert_not_verified("h7g_branch_local_assume_does_not_discharge_cx");
    assert_not_verified("h7h_nested_closure_assume_does_not_discharge_cx");
}

#[test]
fn a15_an_in_body_assume_still_discharges_its_own_body() {
    // The retained capability. Together with `h7g`/`h7h` this is the whole rule:
    // an `assume!` in a closure body is that body's hypothesis, it reaches
    // exactly the obligations it dominates, and it never reaches the parent.
    assert_verified("a15_body_assume_discharges_its_own_body_ok");
}

#[test]
fn a16_a_closure_defined_in_a_dead_branch_carries_no_obligation() {
    assert_verified("a16_dead_branch_definition_ok");
}

// ── ROUND-3: a CONDITIONAL rebind is not a kill ─────────────────────────────
//
// THE DEFECT: `ClosureUseScan::visit_expr_assign` treated EVERY write to the
// closure local as a KILL, so a rebind on ONE arm of an `if` made the later
// `g(a, 0)` the only classified use and the definition site emitted nothing —
// while `reapply_common_branch_exec_closure_rebinds` had already cleared
// `exec_closure_defs["g"]` for a one-arm rebind, so the call site emitted
// nothing either. `e20b` is the decisive pair: DELETING the call
// counterexamples, i.e. adding a use made an unchecked closure LESS checked.
//
// THE FIX: a write is a kill only when it is UNCONDITIONAL — at conditional
// depth zero, outside every loop body and every nested closure, or through an
// `if`/`else` BOTH of whose branches unconditionally write. A conditional write
// leaves the old binding live on the complementary path and is classified as an
// escape. `a17`/`a18`/`a19` are the three over-rejection twins, and `a18` is a
// capability the first increment had LOST.

#[test]
fn e20_one_arm_rebind_then_called_is_checked() {
    assert_not_verified("e20_one_arm_rebind_then_called_cx");
}

#[test]
fn e20b_the_decisive_pair_deleting_the_call_still_counterexamples() {
    // Mutation-sensitive by construction: `e20` and `e20b` differ ONLY by the
    // presence of `let _ = g(a, 0u64);`. If `e20` ever verifies again while
    // this one does not, the check has become disable-able by adding a use.
    let v = verdict("e20b_one_arm_rebind_not_called_cx");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "the call-free half of the decisive pair must counterexample; got {v:?}"
    );
}

#[test]
fn e21_else_only_rebind_then_called_is_checked() {
    assert_not_verified("e21_else_only_rebind_then_called_cx");
}

#[test]
fn e22_match_arm_rebind_then_called_is_checked() {
    assert_not_verified("e22_match_arm_rebind_then_called_cx");
}

#[test]
fn e23_loop_rebind_then_called_is_checked() {
    assert_not_verified("e23_loop_rebind_then_called_cx");
}

#[test]
fn a17_honest_one_arm_rebind_fails_closed() {
    // Over-rejection, kept on purpose: after a conditional rebind the join
    // leaves `g` bound to an invalidation poison, and an application of a
    // function value whose binding is not modelled is refused at extraction
    // (its requires could not be proven at the call). Both bodies are total,
    // so this program is true; the answer must still never be `Verified`
    // without that proof.
    assert_not_verified("a17_one_arm_rebind_honest_ok");
}

#[test]
fn a18_unconditional_straightline_rebind_verifies() {
    // The capability the first increment lost and round 3 restored: an
    // unconditional kill proves the first literal's body can never run.
    assert_verified("a18_unconditional_straightline_rebind_ok");
}

#[test]
fn a19_both_arms_differing_safe_rebind_fails_closed() {
    // Same over-rejection as `a17`: the two arms bind different literals, so
    // the join poisons `g` and its application is refused at extraction.
    assert_not_verified("a19_both_arms_differing_safe_rebind_ok");
}

// ── ROUND-3's ghost-CONSTRUCTOR override, RE-KEYED IN ROUND 6 ───────────────

#[test]
fn a40_a42_a_ghost_constructor_is_a_ghost_receiver() {
    // ROUND 6 RE-KEY, WITH ITS COUNTER-EVIDENCE NAMED. Round 3 pinned
    // `e24`/`e25` — an exec-SPELLED parameter at `Seq::new` is checked — on the
    // theory that a spec closure's parameter is never a finite-width scalar.
    // The corpus's own cardinal spec surface refutes that theory: the lib
    // fixtures `vc_extraction::tests::seq_concrete_ext_eq::{auto_extensionality_syntax2_port_verifies,
    // concrete_generator_vs_push_chain_speceq_verifies}` write
    // `SpecFn::new(|i: usize| 10i32 * (i as i32))`, were GREEN AT THE MERGE BASE,
    // and round 3 turned both into a `Counterexample` over an arbitrary `i`
    // (bisected; rounds 3-5 never ran `-p trust-vc-core --lib`). That is
    // requirement 2's over-rejection, and the parameter SPELLING is the wrong
    // reading — the same wrong reading this campaign removed from the combinator
    // rule. A ghost constructor builds a SPEC value: the closure it is handed is
    // a spec function, its body never executes, and spec arithmetic cannot panic.
    //
    // The pins below are `assert_verified`, not an agreement pin: the residual
    // did not merely move, it closed by a deliberate rule change, and
    // requirement 4 says a closed residual is re-keyed to the REAL verdict.
    assert_verified("a40_ghost_ctor_exec_param_is_spec_ok");
    assert_verified("a41_ghost_ctor_exec_param_named_is_spec_ok");
    // The lib fixtures' exact shape, pinned here too so the integration suite
    // sees it move even if the lib suite is not run.
    assert_verified("a42_specfn_new_exec_param_is_spec_ok");
}

#[test]
fn e24c_e24d_a_second_use_still_reaches_the_check() {
    // WHAT ROUND 3'S OVERRIDE ACTUALLY PROTECTED IS NOT LOST, and this is where
    // that protection really lives: `ClosureUseScan`. Only a closure whose SOLE
    // use is the spec constructor is skipped. Give the same exec-bodied closure
    // a SECOND use — an escape to a higher-order function, or a direct call —
    // and it is checked again. Without this pin the re-key above would be a
    // deletion; with it, the campaign's own rule (a use may never REMOVE an
    // obligation) is still exercised at the constructor sink.
    assert_not_verified("e24c_ghost_ctor_plus_escape_cx");
    assert_not_verified("e24d_ghost_ctor_plus_call_cx");
}

#[test]
fn a20_honest_exec_closure_at_a_ghost_constructor_verifies() {
    assert_verified("a20_ghost_ctor_exec_param_honest_ok");
}

// ── ROUND-3: the disclosed over-approximation, pinned as intended ───────────

#[test]
fn x1_unguarded_arithmetic_on_a_fresh_parameter_is_rejected() {
    // A DISCLOSED CAPABILITY REGRESSION against the merge base, pinned here so
    // it cannot be re-introduced silently in either direction. The definition
    // site knows NOTHING about the parameter (`e10`/`e12` pin exactly that), so
    // `x + 1` is genuinely refutable over an arbitrary `u64`. Narrowing it would
    // mean giving the frame a fact it must not have.
    assert_not_verified("x1_unguarded_param_arith_is_rejected_cx");
    // Round 4: SUBTRACTION is a fourth instance of the same class. Round 3's
    // disclosure named `+`, `*` and the ghost-constructor `+` only.
    assert_not_verified("x1c_unguarded_param_sub_is_rejected_cx");
    // ROUND-6 RE-KEY, and the THIRD over-rejection round 3's constructor
    // override caused. The ghost-CONSTRUCTOR instance (`x1b`) is NOT this class
    // at all: the receiver is a SPEC constructor, so `i + 1u64` is spec
    // arithmetic in a body that never runs. It verified at the merge base, round
    // 3 made it a rejection, and it verifies again — pinned as `a46` with the
    // real verdict rather than left asserting a rejection that is wrong.
    assert_verified("a46_ghost_ctor_param_arith_ok");
}

#[test]
fn a21_guarded_arithmetic_on_a_fresh_parameter_verifies() {
    // The remedy twin, and the reason `x1` is an over-approximation rather than
    // a wall: guard the arithmetic and the identical shape verifies.
    assert_verified("a21_guarded_param_arith_ok");
}

// ── ROUND-3: the macro boundary is the LITERAL, not the name ────────────────

#[test]
fn w2_a_named_closure_inside_a_macro_token_stream_is_checked() {
    // The closed half of the macro residual: an ident inside an opaque token
    // stream is an unclassified use, so the definition site checks the body.
    // The open half (`vec![|x: u64, y: u64| x / y]`) is deliberately NOT pinned
    // — see the residual note in this file's header.
    assert_not_verified("w2_macro_named_closure_cx");
}

// ── ROUND-3b: the sibling arm of a both-arms kill ───────────────────────────

#[test]
fn e26_a_both_arms_kill_still_scans_every_arm() {
    // The one way round 3's kill rule could be wrong: the arms of an
    // `if`/`else` are ALTERNATIVE paths, so stopping the scan at the first
    // arm's write hid what the OTHER arm did with the still-live original.
    assert_not_verified("e26_sibling_arm_escape_after_a_both_arms_kill_cx");
}

#[test]
fn a22_the_sibling_arm_shape_still_verifies_when_honest() {
    assert_verified("a22_sibling_arm_escape_after_a_both_arms_kill_ok");
}

// ── ROUND-4: the IN-LOOP define-and-call, and the arm-local kill ────────────

#[test]
fn e27_defined_and_called_inside_a_loop_is_checked() {
    // THE THIRD CORNER. `e14` = defined outside / called inside; `e19` = defined
    // inside / escapes; this one = defined inside AND called inside, which was
    // checked at neither site because the block-local use scan could not see the
    // enclosing loop and the call-site lane bails in one.
    assert_not_verified("e27_defined_and_called_inside_a_loop_cx");
}

#[test]
fn e27b_the_decisive_pair_deleting_the_in_loop_call_still_counterexamples() {
    // The criterion this round used: adding a USE must never make an unchecked
    // closure LESS checked. This half counterexampled before the fix too.
    assert_not_verified("e27b_defined_inside_a_loop_never_called_cx");
}

#[test]
fn e27c_the_in_loop_call_with_a_symbolic_divisor_is_checked() {
    assert_not_verified("e27c_defined_and_called_inside_a_loop_symbolic_cx");
}

#[test]
fn a23_honest_in_loop_define_and_call_verifies() {
    // Over-rejection control: LOAD-SENSITIVE for the documented `a9`/`a14`
    // reason (the goal is a loop invariant). Re-run ALONE before attributing a
    // red here to the planner.
    assert_verified("a23_defined_and_called_inside_a_loop_honest_ok");
}

#[test]
fn e28_immediately_invoked_literal_inside_a_loop_is_checked() {
    // The planner's OTHER skip had the same hole: the immediately-invoked
    // literal defers to a call-site lane that does not run inside a loop.
    assert_not_verified("e28_immediately_invoked_literal_inside_a_loop_cx");
}

#[test]
fn a23b_honest_immediately_invoked_literal_inside_a_loop_verifies() {
    assert_verified("a23b_immediately_invoked_literal_inside_a_loop_honest_ok");
}

#[test]
fn e29_defined_and_called_inside_a_for_loop_is_checked() {
    assert_not_verified("e29_defined_and_called_inside_a_for_loop_cx");
}

#[test]
fn a25_honest_for_loop_define_and_call_verifies() {
    assert_verified("a25_defined_and_called_inside_a_for_loop_honest_ok");
}

#[test]
fn a24_an_escape_after_an_arms_own_write_verifies() {
    // THE OVER-REJECTION round 3b opened and this round closed: a use placed
    // AFTER an arm's own unconditional write denotes the NEW value, so charging
    // it to the original (whose body can never run on that path) rejected a
    // program that verified at the merge base.
    assert_verified("a24_escape_after_an_in_arm_write_ok");
}

#[test]
fn e30_the_arm_local_kill_only_moves_the_obligation() {
    // The liar twin of `a24`: the arm-local kill must not delete the obligation,
    // only relocate it to the literal that actually escapes.
    assert_not_verified("e30_escape_after_an_in_arm_write_of_an_unsafe_literal_cx");
}

// ── ROUND-4: the call-site-uninstrumentable guard gets its discriminator ────

#[test]
fn e31_a_call_the_lane_cannot_instrument_is_not_coverage() {
    // The guard round 3 shipped without a named discriminating pin. The body
    // re-binds parameter `y`, so `maybe_emit_invoked_exec_closure_arith_safety`
    // bails; treating the direct call as coverage would leave the body checked
    // at neither site. Neutralize `closure_is_call_site_instrumentable` in
    // `closure_uses_are_covered` and exactly this pin goes red.
    assert_not_verified("e31_body_rebinds_a_param_then_called_cx");
}

#[test]
fn a26_an_uninstrumentable_call_with_an_honest_body_verifies() {
    assert_verified("a26_body_rebinds_a_param_honest_ok");
}

// ── ROUND-4: the disclosed residuals become EXECUTABLE ──────────────────────

#[test]
fn u1_untyped_exec_combinator_parameter_is_checked() {
    // RE-KEYED IN ROUND 5, exactly as the round-4 agreement pin asked to be when
    // the residual moved. This was an agreement pin over a false-`Verified`;
    // the receiver now resolves as an EXEC `Vec<u64>`, so the skip is off and
    // the body is checked. The honest twin must still verify.
    assert_not_verified("u1_untyped_combinator_divzero_cx");
    assert_verified("u1b_untyped_combinator_honest_control");
}

#[test]
fn u1c_partially_annotated_parameter_list_is_checked() {
    // The second re-key: `closure_params_are_written_exec_scalars` still
    // requires EVERY parameter, but it is no longer the only discriminator, so a
    // partially annotated list at an exec receiver no longer buys the skip.
    assert_not_verified("u1c_partially_annotated_divzero_cx");
    assert_verified("u1d_partially_annotated_honest_control");
}

#[test]
fn u1e_the_ghost_constructor_sink_is_spec_by_rule_not_by_accident() {
    // RE-KEYED IN ROUND 6 (requirement 4). Round 5 held these as an AGREEMENT
    // pin because the skip "looked at neither body" and its answer was an
    // accident of a name list. It is no longer an accident: a ghost constructor
    // is the strongest ghost receiver there is, and requirement 2 mandates that
    // a spec closure keeps verifying. So the verdict itself is pinned, in both
    // halves — the divzero body AND its honest twin — and `d5` below keeps the
    // no-sink half pinned so the DIVERGENCE stays visible and disclosed.
    assert_verified("u1e_untyped_ghost_ctor_divzero_residual");
    assert_verified("u1f_untyped_ghost_ctor_honest_control");
}

#[test]
fn residual_route_c_macro_opacity_is_not_a_closure_defect() {
    // A closure literal in a `vec!` element is checked at its definition, and
    // is refuted exactly as plain arithmetic in the same macro is. The guarded
    // twin verifies. The constant-divisor control is refused by the encoder
    // (it is an `Error` outside a macro too), so it is pinned as a non-verify.
    // Discriminator: without the element plan (`with_vec_element_closure_plan`)
    // `w1` is `Verified`.
    assert_counterexample("w1_macro_closure_literal_residual");
    assert_verified("w1c_macro_closure_literal_guarded_ok");
    assert_same_verdict(
        "w1_macro_closure_literal_residual",
        "w1d_macro_plain_arith_param_control",
    );
    assert_not_verified("w1b_macro_plain_arith_control");
}

/// Discriminator: without the element plan `w1e` is `Verified`.
#[test]
fn route_c_macro_closure_literal_forms_are_checked() {
    assert_counterexample("w1e_macro_repeat_closure_literal_cx");
    assert_counterexample("w1f_macro_nested_closure_literal_cx");
}

/// Discriminator: planning the element at depth zero skips the invoked
/// literal as covered by the call-site lane, which does not run in a loop
/// body, and `w1g` is `Verified`.
#[test]
fn route_c_macro_element_plan_uses_the_enclosing_loop_depth() {
    assert_counterexample("w1g_macro_invoked_literal_in_loop_cx");
    assert_verified("w1h_macro_invoked_literal_safe_ok");
}

/// Discriminator: planning the element with only its own bindings classifies
/// `v` by the ghost parameter, skips the literal as a spec closure, and `w1i`
/// is `Verified`.
#[test]
fn route_c_macro_element_plan_uses_the_function_lets() {
    assert_counterexample("w1i_macro_shadowed_ghost_receiver_cx");
    assert_verified("w1j_macro_ghost_receiver_spec_closure_ok");
}

#[test]
fn a27_a_spec_closure_bound_inside_a_loop_still_verifies() {
    // THE NARROWING CONTROL for round 4's depth carrying, and a measured
    // over-rejection while the seeding was wider: the enclosing depth gates the
    // COVERING-CALL classification only. A ghost argument defers to no lane, so
    // depth is irrelevant to it — seeded there, this spec closure reached a
    // definition-site check and its ghost body's `* 10` came back
    // `NotProved { category: Incompleteness }`.
    assert_verified("a27_spec_closure_bound_inside_a_loop_ok");
}

#[test]
fn a28_an_inner_closure_defined_and_called_in_an_outer_one_verifies() {
    assert_verified("a28_inner_closure_defined_and_called_in_an_outer_closure_ok");
}

// ── ROUND 5: THE GHOST-SINK SKIP READS THE RECEIVER ─────────────────────────

#[test]
fn n1_a_named_untyped_closure_at_an_exec_combinator_is_refuted() {
    // The NAMED spelling: the literal is written at its binding, so the receiver
    // is reached through `ClosureUseScan` rather than the planner's inline path.
    // Pinned as a REFUTATION, not merely a non-verify.
    assert_counterexample("n1_named_untyped_exec_map_cx");
}

#[test]
fn n1b_the_honest_named_untyped_twin_still_verifies() {
    assert_verified("n1b_named_untyped_exec_map_ok");
}

#[test]
fn n2_an_untyped_exec_map_parameter_is_minted_and_refuted() {
    // THE PIN THAT DISCRIMINATES THE INFERENCE. Neutralize the receiver-element
    // sort carried to `declare_closure_params_at_def_site` and this becomes an
    // `unresolved variable` incompleteness — still a non-verify, so only an
    // exact-verdict pin can see it.
    assert_counterexample("n2_untyped_exec_map_div_by_param_cx");
}

#[test]
fn n2b_a_guarded_untyped_exec_map_parameter_verifies() {
    assert_verified("n2b_untyped_exec_map_guarded_param_ok");
}

#[test]
fn n3_a_let_annotated_vec_receiver_is_exec() {
    assert_not_verified("n3_local_vec_annotation_untyped_cx");
}

#[test]
fn n3b_a_let_annotated_vec_receiver_keeps_its_honest_twin() {
    assert_verified("n3b_local_vec_annotation_untyped_ok");
}

#[test]
fn n4_an_array_receiver_is_exec() {
    assert_not_verified("n4_array_param_untyped_cx");
}

#[test]
fn n4b_an_array_receiver_keeps_its_honest_twin() {
    assert_verified("n4b_array_param_untyped_ok");
}

#[test]
fn n5_a_slice_receiver_is_exec() {
    assert_not_verified("n5_slice_param_untyped_cx");
}

#[test]
fn n5b_a_slice_receiver_keeps_its_honest_twin() {
    assert_verified("n5b_slice_param_untyped_ok");
}

#[test]
fn n6_a_fold_with_an_untyped_accumulator_is_checked() {
    assert_not_verified("n6_untyped_exec_fold_both_cx");
}

#[test]
fn n6b_a_fold_with_an_untyped_accumulator_keeps_its_honest_twin() {
    // The accumulator's sort comes from the INITIAL VALUE, not from the
    // receiver's elements; without that split this honest body fails closed.
    assert_verified("n6b_untyped_exec_fold_both_ok");
}

#[test]
fn n8_a_fold_accumulator_takes_its_sort_from_the_init() {
    // THE PIN FOR THE ACCUMULATOR SPLIT. A `Vec<u64>` folded from a `0u32` seed
    // has a `u32` accumulator; minting it at the receiver's ELEMENT sort still
    // refutes, so only the reported MODEL can see the difference — and a
    // counterexample that names a `u64` for a `u32` program variable
    // misdescribes the program. Neutralize the `folding` split and exactly this
    // pin goes red (measured: the binding comes back `u64`).
    let v = verdict("n8_fold_accumulator_sort_from_init_cx");
    let VerifyResult::Counterexample { bindings, .. } = &v else {
        panic!("EXPECTED A REFUTATION: `n8_fold_accumulator_sort_from_init_cx` got {v:?}");
    };
    let acc = bindings
        .iter()
        .find(|binding| binding.display_name.starts_with("acc__closureparam"))
        .unwrap_or_else(|| panic!("no accumulator binding in the model: {bindings:?}"));
    assert_eq!(
        acc.ty, "u32",
        "ACCUMULATOR SORT: the fold seed is `0u32`, so the accumulator is a u32, \
         not the receiver's element sort; got {acc:?}"
    );
}

#[test]
fn n8b_the_honest_fold_accumulator_twin_verifies() {
    assert_verified("n8b_fold_accumulator_sort_from_init_ok");
}

#[test]
fn n7_an_unresolvable_receiver_fails_closed() {
    // REQUIREMENT 3, pinned. A receiver the classifier cannot resolve does NOT
    // buy the ghost skip. The measured fail-closed outcome is an `unresolved
    // variable` incompleteness — a sound non-verify, never a `Verified`.
    assert_not_verified("n7_unresolved_receiver_untyped_cx");
}

#[test]
fn n9_a_ghost_shadow_does_not_reclassify_an_earlier_exec_use() {
    // The receiver environment's `let` map is FLAT over the body, so a binding
    // that shadows a function parameter could decide uses that PRECEDE it.
    // Neutralize the disagreement rule (let the shadow win) and exactly this pin
    // goes red — with a false-`Verified`, because the earlier exec `.map` would
    // inherit the ghost shadow's skip.
    assert_not_verified("n9_ghost_shadow_does_not_reclassify_earlier_exec_use_cx");
}

#[test]
fn n9b_the_ghost_shadow_honest_twin_verifies() {
    assert_verified("n9b_ghost_shadow_honest_twin_ok");
}

// ── ROUND 5: THE DECISIVE PAIR IS THE BAR, AND IT IS EXECUTABLE ─────────────

#[test]
fn d_adding_a_ghost_sink_never_removes_an_obligation() {
    // Every exec-sink shape this round touches, each against the IDENTICAL body
    // with the sink deleted. This is the pin that would have caught route A on
    // this branch, and the shape `e27b` already uses for the loop case.
    for (with_sink, without_sink) in [
        ("u1_untyped_combinator_divzero_cx", "d1_u1_no_sink_twin"),
        ("u1c_partially_annotated_divzero_cx", "d2_u1c_no_sink_twin"),
        ("n1_named_untyped_exec_map_cx", "d3_n1_no_sink_twin"),
        ("n2_untyped_exec_map_div_by_param_cx", "d3_n1_no_sink_twin"),
        ("n6_untyped_exec_fold_both_cx", "d4_n6_no_sink_twin"),
        ("n7_unresolved_receiver_untyped_cx", "d1_u1_no_sink_twin"),
    ] {
        assert_sink_does_not_weaken(with_sink, without_sink);
    }
}

#[test]
fn d5_the_ghost_constructor_no_sink_twin_is_checked() {
    // THE OTHER HALF of the one pair that still diverges (`u1e`). The bare
    // literal `let _g = |i| 10u64 / i;` reaches a definition-site check and
    // fails closed; handing it to `Seq::new` verifies. That pair is recorded in
    // the header as the REMAINING route-A residual, and this pin keeps its
    // no-sink half honest so the divergence cannot be quietly erased from
    // either end.
    assert_not_verified("d5_u1e_no_sink_twin");
}

// ── ROUND 5: THE GHOST SURFACE, RE-MEASURED ────────────────────────────────

#[test]
fn a29_a37_the_ghost_surface_still_verifies() {
    // REQUIREMENT 2. Eleven spec-context shapes, every one of them an UNTYPED
    // spec closure or a quantifier body containing arithmetic, at a receiver the
    // classifier must resolve as ghost: a `Seq`/`Set`/`Map` parameter, a
    // `Seq::new(..)` result, a `let`-annotated ghost local, a `.view()` ghost
    // view, and the named spellings of two of them.
    for func in [
        "a29_ghost_seq_param_map_untyped_ok",
        "a30_ghost_seq_param_filter_untyped_ok",
        "a31_ghost_seq_param_fold_untyped_ok",
        "a32_ghost_ctor_chained_combinator_untyped_ok",
        "a33_ghost_set_map_untyped_ok",
        "a34_ghost_map_values_untyped_ok",
        "a35_local_ghost_seq_annotation_untyped_ok",
        "a36_spec_quantifier_body_arith_ok",
        "a37_named_untyped_ghost_seq_ok",
        "a38_named_untyped_ghost_seq_fold_ok",
        "a39_ghost_view_untyped_ok",
    ] {
        assert_verified(func);
    }
}

// ── ROUND 5: THE SECOND DISCLOSED CAPABILITY REGRESSION ────────────────────

#[test]
fn x2_the_unresolvable_receiver_cost_is_now_the_chained_receiver_only() {
    // RE-KEYED IN ROUND 6 (requirement 4), and the half that closed is a
    // CAPABILITY GAIN. Round 5 disclosed a BRANCH receiver
    // (`(if c { v } else { v }).map(|x| x / 2u64)`) as collateral damage from
    // failing closed; round 6 classifies a branch by its ARMS, so it resolves
    // and the honest body verifies again — pinned as `assert_verified`, not left
    // asserting a rejection that no longer happens.
    assert_verified("a45_branch_receiver_honest_ok");
    // The half that REMAINS: a combinator CHAIN re-types its elements, so an
    // exec chain carries no element sort forward and an untyped parameter over
    // it still has nothing to mint. Disclosed, not hidden.
    assert_not_verified("x2b_chained_exec_receiver_honest_is_rejected");
}

#[test]
fn x2c_the_narrowing_control_a_resolved_exec_receiver_still_verifies() {
    // The cost is EXACTLY the unresolvable receiver and nothing wider: the same
    // honest body at a receiver the classifier does resolve keeps verifying.
    assert_verified("u1b_untyped_combinator_honest_control");
    assert_verified("n3b_local_vec_annotation_untyped_ok");
}

// ── ROUND 5: THE ROUTE-A RESIDUAL THAT REMAINS ─────────────────────────────

#[test]
fn u1k_a_ghost_view_is_a_spec_seq_by_rule() {
    // RE-KEYED IN ROUND 6, for the same reason as `u1e`. `v@` (desugared
    // `.view()`) of an exec `Vec` IS a spec `Seq`; a closure over it is a spec
    // function and its body never executes. Round 5 filed that under "route-A
    // residual" because the rule it had could not say WHY; round 6's rule says
    // why — a positively-identified ghost receiver — so the verdict is pinned.
    assert_verified("u1k_ghost_view_divzero_residual");
    assert_verified("u1l_ghost_view_honest_control");
}

// ── ROUND 6: AN EXEC STD SET/MAP IS NOT A GHOST COLLECTION ─────────────────

#[test]
fn p1_p6_an_exec_std_set_or_map_is_checked() {
    // BLOCKER, ROUND 5's OWN PATTERN ON THE EXEC SIDE IT DECLARED CLOSED.
    // `BTreeSet<u64>`/`HashSet<u64>` parse to `TrustVcType::Set` and
    // `BTreeMap`/`HashMap` to `Map` — the SAME sorts the spec `Set`/`Map` use —
    // and round 5 granted the ghost skip to anything that merely modeled as one
    // of those. So `v.map(|x| x / 0u64)` on an exec `BTreeSet` published
    // `Verified` while the identical no-sink twin was checked: adding a use
    // removed an obligation. Round 6 decides it from the ORIGIN SPELLING, the
    // same reading that separates `Vec` from `Seq`.
    for func in [
        "p1_btreeset_map_untyped_cx",
        "p2_btreeset_no_param_sort_cx",
        "p3_hashset_map_untyped_cx",
        "p4_btreemap_map_values_cx",
        "p5_hashmap_map_values_cx",
        "p6_let_annotated_btreeset_cx",
        "p6c_unannotated_btreeset_local_cx",
    ] {
        assert_not_verified(func);
    }
    // The MINT reached the definition site: the divisor is the PARAMETER, so
    // only a carried element sort can turn this into a refutation rather than an
    // `unresolved variable` incompleteness.
    assert_counterexample("p1c_btreeset_div_by_param_cx");
}

#[test]
fn p1b_p6b_the_honest_exec_set_map_twins_still_verify() {
    // The over-rejection controls. Closing the exec side must not cost the
    // honest body, and the mint is what keeps it: without the element sort these
    // four are incompletenesses, not `Verified`.
    for func in [
        "p1b_btreeset_map_untyped_ok",
        "p3b_hashset_map_untyped_ok",
        "p4b_btreemap_map_values_ok",
        "p6b_let_annotated_btreeset_ok",
    ] {
        assert_verified(func);
    }
}

#[test]
fn a43_a44_the_spec_set_and_map_surface_is_untouched() {
    // REQUIREMENT 2, and the answer to round 5's false dichotomy. The header
    // defended reading every `Set`/`Map` as ghost by claiming the alternative
    // was rejecting the `Set`/`Map` spec surface. It is not: the SPEC spelling
    // keeps the skip, so closing the exec side costs no measured spec surface.
    assert_verified("a43_spec_set_divzero_still_skipped");
    assert_verified("a44_spec_map_values_untyped_ok");
}

#[test]
fn d6_adding_an_exec_set_or_map_sink_never_removes_an_obligation() {
    // THE DECISIVE-PAIR BAR for the family round 5 left prose-only. Each body is
    // measured WITH the sink and with the sink DELETED; the sink may never turn
    // a non-verify into a `Verified`.
    for (with_sink, without_sink) in [
        ("p1_btreeset_map_untyped_cx", "d1_u1_no_sink_twin"),
        ("p2_btreeset_no_param_sort_cx", "d6_p2_no_sink_twin"),
        ("p1c_btreeset_div_by_param_cx", "d3_n1_no_sink_twin"),
        ("p3_hashset_map_untyped_cx", "d1_u1_no_sink_twin"),
        ("p4_btreemap_map_values_cx", "d1_u1_no_sink_twin"),
        ("p5_hashmap_map_values_cx", "d1_u1_no_sink_twin"),
        ("p6_let_annotated_btreeset_cx", "d1_u1_no_sink_twin"),
        ("p6c_unannotated_btreeset_local_cx", "d6_p2_no_sink_twin"),
        ("p11_struct_field_exec_vec_cx", "d6_p2_no_sink_twin"),
        ("p12_struct_field_nested_vec_cx", "d6_p2_no_sink_twin"),
        ("p13_if_else_exec_cx", "d1_u1_no_sink_twin"),
        ("p15_if_else_one_unresolved_arm_cx", "d6_p2_no_sink_twin"),
        ("p15b_if_else_ghost_and_exec_arms_cx", "d6_p2_no_sink_twin"),
        ("e24c_ghost_ctor_plus_escape_cx", "d3_n1_no_sink_twin"),
        ("e24d_ghost_ctor_plus_call_cx", "d3_n1_no_sink_twin"),
    ] {
        assert_sink_does_not_weaken(with_sink, without_sink);
    }
}

// ── ROUND 6: THE RECEIVERS ROUND 5 COULD ONLY FAIL CLOSED ON ───────────────

#[test]
fn p7_p14_unresolvable_ghost_receivers_are_recovered() {
    // REQUIREMENT 2, the half round 5's disclosure got wrong. Round 5 claimed
    // the cost of failing closed was "exactly the unresolvable receiver and
    // nothing wider" and measured only exec twins; measured on the SPEC side, a
    // struct field holding a `Seq<int>`, a tuple field, and a branch receiver
    // all went from `Verified` to an `unresolved variable` incompleteness. A
    // struct field holding a spec collection is ordinary spec code.
    //
    // Two readings recover them, neither of which needs provenance that does not
    // exist: an UNBOUNDED MATHEMATICAL element sort (no exec container can hold
    // an `int`/`nat`/`Real`) and AGREEING BRANCH ARMS.
    for func in [
        "p7_struct_field_ghost_seq_ok",
        "p8_tuple_field_ghost_seq_ok",
        "p9_if_else_ghost_ok",
        "p14_match_ghost_ok",
    ] {
        assert_verified(func);
    }
}

#[test]
fn p10_the_map_index_receiver_is_not_what_is_rejected() {
    // ATTRIBUTION, not a verdict claim. `m[k].map(|i| i + 1)` does not verify —
    // but neither does `m[k]` alone, because a `Map` INDEX carries a domain
    // obligation of its own. Pinning their AGREEMENT says exactly what is known:
    // the closure over the indexed spec `Seq` is not the thing being rejected.
    // If the index obligation is ever discharged while the closure beside it is
    // not, this fires and the attribution must be redone.
    assert_same_verdict(
        "p10_map_index_ghost_ok",
        "p10b_map_index_no_closure_control",
    );
}

#[test]
fn p11_p15b_the_exec_half_of_the_same_two_readings_stays_checked() {
    // THE SOUNDNESS HALF, and the boundary of each new reading.
    //
    // `p11` — a struct field holding a `Vec<u64>` has exec-width elements, so it
    // gets NO ghost reading and is checked.
    // `p12` — a `Vec<Vec<u64>>` models as `Seq(Seq(Uint))`. "The element is
    // itself a collection" is NOT ghost evidence; admitting it would hand the
    // skip to an ordinary exec `Vec` of `Vec`s.
    // `p13` — two exec arms are an EXEC receiver, not a skip.
    // `p15`/`p15b` — arm DISAGREEMENT fails closed, including the case that
    // matters for soundness: a ghost arm beside an exec arm must not lend the
    // exec arm its skip.
    for func in [
        "p11_struct_field_exec_vec_cx",
        "p12_struct_field_nested_vec_cx",
        "p13_if_else_exec_cx",
        "p15_if_else_one_unresolved_arm_cx",
        "p15b_if_else_ghost_and_exec_arms_cx",
    ] {
        assert_not_verified(func);
    }
}

#[test]
fn x3_a_spec_seq_field_with_exec_width_elements_is_recovered() {
    // ROUND 6'S DISCLOSED OVER-REJECTION, CLOSED IN ROUND 7 — and re-keyed from
    // `assert_not_verified` to the verdict it now has. A struct FIELD's origin
    // spelling used to reach nothing (`StructDef` records modeled field types
    // only), so a spec `Seq<u64>` field was indistinguishable from a `Vec<u64>`
    // field and failed CLOSED. Round 7 records the field's own spelling and the
    // spec field is spec code again.
    //
    // THE DECISIVE PAIR, and the liar twin this `Verified` needs: ONE body
    // (`|i| i + 1`, which overflows at `u64`), ONE element width, TWO SPELLINGS.
    // `Seq<u64>` verifies because a closure over a spec collection is a spec
    // function; `Vec<u64>` is checked, mints `u64` and REFUTES. If the recovery
    // were a blanket "fields are ghost", `x3b` would verify too.
    assert_verified("x3_struct_field_ghost_seq_exec_elem_ok");
    assert_counterexample("x3b_exec_vec_u64_field_same_body_cx");
}

// ── ROUND 6b: THE MINT'S WIDTH IS NOT THE FIRST RECEIVER'S ─────────────────

#[test]
fn m1_m3_a_second_receiver_may_not_reuse_the_first_ones_width() {
    // THE BLOCKER ROUND 6 LEFT, measured by the round-6 review. One
    // definition-site frame serves EVERY application of a named literal, so the
    // sort minted from one receiver is applied to all of them — and round 5
    // took the FIRST exec receiver's and kept it. Measured on the round-6 tip:
    //
    //   let g = |x| if x < 100 { x * 3 } else { 0 };
    //   let _ = v.map(g);   // v: Vec<u64>   -> mints u64
    //   let _ = w.map(g);   // w: Vec<u8>    -> OVERFLOWS, and is discharged
    //
    // published `Verified` (`m1`), while the identical body with that FIRST use
    // DELETED counterexamples (`m1b`) and the same two uses in the other order
    // counterexample as well (`m1c`). That is a false-`Verified` of a genuine
    // `u8` overflow AND an adding-a-use-disables-the-check pair — the campaign's
    // declared blocker — reached by ordinary code: one helper closure applied to
    // two collections of different element width.
    //
    // `m3` is the same false verify with the second receiver UNRESOLVED
    // (`w.to_vec()`), which round 5's rule also served from the `u64` mint. Both
    // were measured `Verified` before the fix and are measured non-verifies
    // after it; the neutralization below reds exactly this test and `m1c` stays
    // green throughout, which is what shows the fix is the agreement and not a
    // blanket refusal to mint.
    assert_not_verified("m1_wide_receiver_first_cx");
    assert_not_verified("m3_unresolved_second_receiver_cx");
    assert_counterexample("m1b_narrow_receiver_only_cx");
    // ORDER INDEPENDENCE is the property the fix buys, and it is pinned as a
    // non-verify rather than as a refutation on purpose: BEFORE the fix the two
    // orders DISAGREED (`m1` `Verified`, `m1c` `Counterexample`), which is how
    // the defect was found; AFTER it neither order mints, so both fail closed
    // into the `unresolved variable` incompleteness. Asserting a counterexample
    // here would be asserting that a borrowed width is still in play.
    assert_not_verified("m1c_narrow_receiver_first_cx");
    // The decisive pair, executable: `m1` is `m1b` plus one added use.
    assert_sink_does_not_weaken("m1_wide_receiver_first_cx", "m1b_narrow_receiver_only_cx");
    assert_sink_does_not_weaken(
        "m3_unresolved_second_receiver_cx",
        "m1b_narrow_receiver_only_cx",
    );
}

#[test]
fn m2_m5_the_agreement_rule_costs_no_honest_verdict_where_the_uses_agree() {
    // OVER-REJECTION CONTROLS. The fix must not be "stop minting": the wide
    // receiver ALONE still mints and still verifies (`m2`), two receivers of the
    // SAME element sort still agree and still verify (`m4`), and disagreeing
    // widths over a body with no width-sensitive obligation still verify
    // (`m5`).
    assert_verified("m2_wide_receiver_only_ok");
    assert_verified("m4_two_same_width_receivers_ok");
    assert_verified("m5_two_widths_no_obligation_ok");
}

#[test]
fn m7_a_ghost_use_does_not_veto_the_mint() {
    // A spec application carries no runtime obligation, so a GHOST use neither
    // needs a sort nor may cancel one an EXEC use established. Without this
    // asymmetry the fix would have swallowed every closure shared between a spec
    // collection and an exec one.
    assert_counterexample("m7_ghost_use_does_not_cancel_the_mint_cx");
}

#[test]
fn m6_the_disclosed_cost_of_refusing_a_borrowed_width() {
    // DISCLOSED CAPABILITY COST, ROUND 6b, pinned rather than left to be
    // rediscovered. An HONEST body applied to a resolved exec receiver and an
    // UNRESOLVED one no longer borrows the resolved width, so it fails closed
    // into an `unresolved variable` incompleteness. It VERIFIED at the merge
    // base (where nothing checked the body at all) and it verified on the
    // round-6 tip (where the borrowed width happened to be right). `m3` is why
    // the borrow cannot stay: the identical shape with a `Vec<u8>` behind the
    // `.to_vec()` was a measured false-`Verified`. `m4` is the narrowing
    // control — the cost is exactly the disagreeing or unresolved receiver.
    assert_not_verified("m6_honest_unresolved_second_receiver_rejected");
}

// ── ROUND 7: THE `int`/`nat` ELEMENT READING IS RETIRED, AND THE FIELD, ────
// ── TUPLE AND INDEX ROUTES READ A MEASURED SPELLING INSTEAD ────────────────

#[test]
fn y1_y2_the_mathematical_element_false_verify_is_closed() {
    // ROUND 6b'S DISCLOSED FALSE VERIFY, CLOSED — re-keyed from the
    // `assert_same_verdict` agreement pin it was held as into real verdicts,
    // which is exactly the signal that pin existed to raise.
    //
    // `positively_ghost_element_sort` granted the ghost skip to any receiver
    // whose modeled ELEMENT sort was `int`/`nat`/`Real`, on the justification
    // "no exec Rust container can hold one — there is no `Vec<int>`".
    // `trust-vc-types` declares `pub type int = i128;` and `pub type nat =
    // u128;`, so that justification was FALSE and `b.data.map(|_x| 10u64 /
    // 0u64)` over a `Vec<int>` FIELD published `Verified` while its no-sink twin
    // did not. The reading is retired outright (there is no sound narrower form:
    // its whole content was a premise about what cannot occur in an exec
    // container, and the premise is untrue), and what replaces it is the
    // field's own ORIGIN SPELLING.
    assert_not_verified("y1_int_elem_exec_field_residual");
    assert_sink_does_not_weaken(
        "y1_int_elem_exec_field_residual",
        "y1c_int_elem_exec_field_no_sink_twin",
    );
    // THE SEAMS NOW AGREE about this one type, which is the inconsistency `y2`
    // was pinned over: the same `Vec<int>` is checked whether it is spelled at
    // the PARAMETER seam or behind a FIELD.
    assert_not_verified("y2_int_elem_exec_parameter_is_checked_cx");
    // NO CAPABILITY COST, measured rather than assumed: the honest twins of both
    // halves still verify. `y1b` was the fixture most at risk — an exec
    // `Vec<int>` field whose element sort (`MathInt`) is deliberately NOT
    // mintable, so the frame gets no parameter sort — and it verifies anyway
    // because the body does not read the parameter. `y1d` is the narrowing
    // control at a mintable width.
    assert_verified("y1b_int_elem_exec_field_honest_control");
    assert_verified("y1d_u64_elem_exec_field_honest_ok");
    assert_verified("y2b_int_elem_exec_parameter_honest_ok");
}

#[test]
fn z1_z5_every_route_the_retired_reading_reached_is_now_checked() {
    // THE FALSE VERIFY, ROUTE BY ROUTE. Each of these carried an `int`/`nat`
    // element behind a receiver whose spelling round 6 could not see, so each
    // bought the ghost skip on an ordinary EXEC container:
    //
    //   `z1` a `Vec<nat>` FIELD           (`nat` is `u128`)
    //   `z2` a `BTreeSet<int>` FIELD      (the `Set` sort, no bounded-len bit)
    //   `z3` a `(Vec<int>, u64)` TUPLE    (component provenance, binding-keyed)
    //   `z4` a `Vec<Vec<int>>` INDEX      (the route round 6b named but never
    //                                      fixtured — `m[i]` has an `int`
    //                                      element and read GHOST)
    //   `z5` a field spelled through a TYPE ALIAS — provenance genuinely
    //        unknown, so it fails CLOSED. Over-rejection is the acceptable
    //        direction and this pins that it is the direction taken.
    for func in [
        "z1_nat_elem_exec_field_cx",
        "z2_int_elem_exec_set_field_cx",
        "z3_int_elem_exec_tuple_cx",
        "z4_index_int_elem_exec_cx",
        "z5_alias_field_unknown_provenance_cx",
    ] {
        assert_not_verified(func);
    }
    // REQUIREMENT 1 on the new routes: adding the sink may never remove an
    // obligation the same body carries without it.
    for (with_sink, without_sink) in [
        ("z1_nat_elem_exec_field_cx", "d6_p2_no_sink_twin"),
        ("z2_int_elem_exec_set_field_cx", "d6_p2_no_sink_twin"),
        ("z3_int_elem_exec_tuple_cx", "d6_p2_no_sink_twin"),
        ("z4_index_int_elem_exec_cx", "d6_p2_no_sink_twin"),
        ("z5_alias_field_unknown_provenance_cx", "d6_p2_no_sink_twin"),
    ] {
        assert_sink_does_not_weaken(with_sink, without_sink);
    }
}

#[test]
fn z5b_z5c_what_retiring_the_element_sort_reading_costs() {
    // MEASURED, NOT LEFT FOR REVIEW TO FIND. The retired reading recovered ANY
    // receiver with an `int`/`nat`/`Real` element, spec or exec alike. Field and
    // tuple provenance give back every spec receiver whose spelling is
    // `Seq`/`Set`/`Map`/`Multiset` — which is the whole `p7`-`p14` surface — but
    // a spec collection reached through a TYPE ALIAS has no recorded spelling at
    // either seam, so it now fails CLOSED. Over-rejection is the acceptable
    // direction and this is the price, pinned at both seams it arises at.
    //
    // CORRECTED BY THE ROUND-7 REVIEW: the alias is NOT the only thing the
    // retirement costs — see `v1_v4_the_retirement_costs_more_than_the_alias`,
    // which measures four more spec receivers round 6 recovered and round 7
    // does not. `p7` is still the narrowing control for the DIRECTLY-spelled
    // field, and that reading stands: a field spelled `Seq<int>` verifies.
    assert_not_verified("z5b_alias_ghost_field_over_rejection");
    assert_not_verified("z5c_alias_ghost_parameter_over_rejection");
    assert_verified("p7_struct_field_ghost_seq_ok");
}

#[test]
fn v1_v4_the_retirement_costs_more_than_the_alias() {
    // ROUND-7 REVIEW FINDING, measured with the `G13` neutralization (the
    // retired element-sort reading restored and NOTHING else changed): four
    // more spec receivers were `Verified` under round 6's reading and are
    // non-verifies now, so the round-7 disclosure that the TYPE ALIAS is "the
    // ONLY thing the retirement costs that provenance does not give back" is
    // refuted by measurement.
    //
    //   `v1` a GENERIC carrier holding a spec `Seq<int>` (field spelling `T`)
    //   `v2` the same carrier holding a spec `Map<int, int>`
    //   `v3` a TUPLE nested below the root binding (`t.0.0`)
    //   `v4` a TUPLE reached through a struct FIELD (`b.t.0`)
    //
    // `v4` is the one that refutes the wording directly: there the cost IS the
    // field, not an alias. All four are OVER-REJECTIONS — the acceptable
    // direction — and this test records them executably so the next round
    // inherits the real cost instead of the claimed one. Closing them needs the
    // origin spelling to survive GENERIC INSTANTIATION and a per-carrier tuple
    // component table, which is a seam of its own.
    for func in [
        "v1_generic_carrier_spec_seq_field_over_rejection",
        "v2_generic_carrier_spec_map_field_over_rejection",
        "v3_nested_tuple_spec_seq_over_rejection",
        "v4_tuple_in_struct_field_spec_over_rejection",
    ] {
        assert_not_verified(func);
    }
    // THE SOUNDNESS HALF, which is what keeps this from being satisfiable by a
    // blanket "generic and nested receivers are ghost": the identical shapes
    // holding an exec `Vec<int>` must stay CHECKED. Both were false `Verified`
    // under the retired reading, so these two are also the round-7 fix's own
    // pins at routes `z1`-`z5` do not reach.
    assert_not_verified("v1b_generic_carrier_exec_vec_field_cx");
    assert_not_verified("v4b_tuple_in_struct_field_exec_cx");
    assert_sink_does_not_weaken(
        "v1b_generic_carrier_exec_vec_field_cx",
        "d6_p2_no_sink_twin",
    );
    assert_sink_does_not_weaken("v4b_tuple_in_struct_field_exec_cx", "d6_p2_no_sink_twin");
    // The narrowing control: the DIRECTLY-spelled field is still recovered, so
    // what these four measure is the missing spelling and not a blanket refusal
    // to read a field.
    assert_verified("p7_struct_field_ghost_seq_ok");
}

#[test]
fn z3b_z3c_the_tuple_component_decisive_pair() {
    // WHY THE TUPLE TABLE IS KEYED BY THE BINDING AND NOT BY THE CARRIER. A
    // tuple's carrier NAME is built from its MODELED element types
    // (`ir_expr::tuple_datatype_name`), so `(Vec<u64>, u64)` and
    // `(Seq<u64>, u64)` name the SAME carrier — a carrier-keyed entry would let
    // one spelling answer for the other. These two fixtures are that pair: ONE
    // body, ONE element width, and the ONLY difference is the spelling of the
    // first component.
    assert_verified("z3b_ghost_seq_u64_tuple_ok");
    assert_counterexample("z3c_exec_vec_u64_tuple_cx");
}

#[test]
fn z6_the_multi_width_agreement_rule_reaches_through_a_field() {
    // REQUIREMENT 3 with round 6b's shape applied through a FIELD. Before this
    // round a field receiver minted NOTHING, so a borrowed width could not arise
    // there; now that fields mint, round 6b's pairwise agreement has to cover
    // them or the closed hole re-opens one seam over.
    //
    //   let g = |x| if x < 100 { x * 3 } else { 0 };   // safe at u64, OVERFLOWS at u8
    //   let _ = b.wide.map(g);     // Vec<u64> field
    //   let _ = b.narrow.map(g);   // Vec<u8>  field
    //
    // `z6` is `z6b` PLUS ONE ADDED USE and must not be weaker for it; `z6c` is
    // the same two uses in the other order, so the verdict is ORDER-INDEPENDENT.
    assert_not_verified("z6_multiwidth_field_cx");
    assert_not_verified("z6c_multiwidth_field_reversed_cx");
    assert_counterexample("z6b_multiwidth_field_narrow_only_cx");
    assert_sink_does_not_weaken(
        "z6_multiwidth_field_cx",
        "z6b_multiwidth_field_narrow_only_cx",
    );
    // THE NARROWING CONTROL: the wide field ALONE still mints and still
    // verifies, so what `z6` measures is the DISAGREEMENT and not a blanket
    // refusal to mint through a field. Without this the test would pass just as
    // well if round 7 had made every field receiver unresolvable.
    assert_verified("z6d_multiwidth_field_wide_only_ok");
}

#[test]
fn z7_the_projection_walk_resolves_each_step_and_the_last_step_decides() {
    // A TWO-STEP PROJECTION (`b.inner.data`). The walk resolves the carrier of
    // each step through the modeled type and reads the provenance of the LAST
    // step, in both directions: an exec `Vec<u64>` two levels down is checked,
    // a spec `Seq<int>` two levels down is spec code.
    assert_not_verified("z7_nested_exec_field_cx");
    assert_sink_does_not_weaken("z7_nested_exec_field_cx", "d6_p2_no_sink_twin");
    assert_verified("z7b_nested_ghost_field_ok");
}

#[test]
fn d7_the_shapes_the_round_6_review_swept() {
    // REQUIREMENT 1, widened. The `d`/`d6` tables cover the `.map`/`.filter`/
    // `.fold` families and the `Set`/`Map` containers; these are the remaining
    // shapes the round-6 review's 32-pair sweep measured — `for_each`, `retain`,
    // a NESTED sink, a sink inside a LOOP, a sink on an UNRESOLVABLE receiver,
    // and a literal handed to BOTH a sink and a higher-order fn, a struct field,
    // or a GHOST sink. Every one is measured no weaker WITH the sink than
    // WITHOUT it.
    for (with_sink, without_sink) in [
        ("d7a_for_each_sink_cx", "d1_u1_no_sink_twin"),
        ("d7b_retain_sink_cx", "d1_u1_no_sink_twin"),
        ("d7c_nested_sink_cx", "d7c_nested_no_sink_twin"),
        ("d7d_sink_inside_a_loop_cx", "d7d_loop_no_sink_twin"),
        ("d7e_unresolvable_receiver_sink_cx", "d1_u1_no_sink_twin"),
        ("d7f_sink_and_higher_order_cx", "d7f_higher_order_only_twin"),
        ("d7g_sink_and_struct_field_cx", "d7g_struct_field_only_twin"),
        ("d7h_ghost_and_exec_sink_cx", "d7h_ghost_sink_only_twin"),
    ] {
        assert_sink_does_not_weaken(with_sink, without_sink);
    }
    // The GHOST-plus-EXEC pair is the one whose no-sink twin VERIFIES (a
    // ghost-only use is a spec function), so `assert_sink_does_not_weaken`
    // returns early on it. Pin the exec half directly so the pair is not
    // vacuous.
    assert_not_verified("d7h_ghost_and_exec_sink_cx");
    assert_verified("d7h_ghost_sink_only_twin");
}

// ── ROUND-7 REVIEW: the projection root was not shadow-guarded ──────────────

/// ROUND-7 REVIEW FINDING, and the sixth "adding something disables the check"
/// route this campaign has found. Round 7 records collection provenance against
/// the DECLARED binding — the field table is keyed by the carrier
/// `get_variable_type` answers with, the tuple table by the binding NAME — and
/// the sink scan is FLAT over the whole body, so nothing re-resolved the root of
/// a field projection. A `let` that REBINDS the root therefore had the
/// parameter's recorded spelling answer for an unrelated value.
///
/// Measured at `7119a236`, cache off: all five `_cx` fixtures below came back
/// `Verified` on bodies that ALWAYS divide by zero. The `Expr::Path` route has
/// carried a shadow rule since round 5 for exactly this reason; the `Expr::Field`
/// route round 7 re-keyed did not get one.
#[test]
fn zzs1_zzs4_a_shadowed_projection_root_is_not_the_declared_binding() {
    for func in [
        "zzs1_tuple_shadow_spec_then_exec_cx",
        "zzs2_tuple_shadow_annotated_cx",
        "zzs3_struct_shadow_cx",
        "zzs4_tuple_shadow_inner_block_cx",
        "zzs4b_tuple_shadow_index_one_cx",
    ] {
        assert_not_verified(func);
        assert_sink_does_not_weaken(func, "d6_p2_no_sink_twin");
    }
    // THE DECISIVE CONTROLS. The identical body with the shadowed parameter
    // RENAMED, or DELETED, was a non-verify at the same commit — so what bought
    // the skip was the NAME of an otherwise unused parameter, and these two must
    // stay non-verifies or the pin above would be measuring the body instead.
    assert_not_verified("zzs1b_shadow_control_param_renamed_cx");
    assert_not_verified("zzs1c_shadow_control_no_tuple_param_cx");
    // A use that PRECEDES the rebind was never affected.
    assert_not_verified("zzs9_use_before_shadow_cx");
}

/// THE LIAR TWIN for the guard above, which is what keeps it from being
/// satisfiable by refusing every projection. An UNSHADOWED spec receiver is
/// still legitimately skipped — a spec closure carries no panic-freedom
/// obligation (`a6`) — so these two must keep verifying with the SAME
/// always-panicking body the `_cx` fixtures use. That is the whole distinction
/// the shadow guard has to draw.
#[test]
fn zzs5_zzs6_the_unshadowed_spec_receiver_is_still_skipped() {
    assert_verified("zzs5_unshadowed_ghost_tuple_ok");
    assert_verified("zzs6_unshadowed_ghost_field_ok");
    // and the round-7 recoveries the guard must not touch.
    assert_verified("p7_struct_field_ghost_seq_ok");
    assert_verified("x3_struct_field_ghost_seq_exec_elem_ok");
    assert_verified("z3b_ghost_seq_u64_tuple_ok");
    assert_verified("z6d_multiwidth_field_wide_only_ok");
}

/// WHAT THE GUARD COSTS, measured rather than assumed. A root that is let-bound
/// and is NOT a shadow resolved no field provenance BEFORE the guard either —
/// `get_variable_type` does not answer for a body-local carrier — so both of
/// these were already over-rejections at `7119a236` and the guard takes nothing
/// away. If a future round teaches the context about local carriers, these two
/// become `assert_verified` and the guard needs the AGREEING-let case, not a
/// blanket refusal.
#[test]
fn zzs7_zzs8_the_shadow_guard_costs_nothing_measured() {
    assert_not_verified("zzs7_local_carrier_ghost_field_over_rejection");
    assert_not_verified("zzs8_local_tuple_ghost_over_rejection");
}

// ── ROUND 8: every binder form is a shadow, not just an ident `let` ─────────

/// ROUND-8 FINDING, and the SEVENTH "adding something disables the check" route
/// this campaign has found. Rounds 5 and 7 both guard a receiver whose NAME is
/// rebound in the body, and both read the SAME map — which was filled only from
/// a `let` whose pattern is a plain ident (`local_ident` answers `None` for
/// every other pattern). Every other binder in a function body was invisible to
/// both guards, so the function PARAMETER of that name kept answering for an
/// unrelated exec value.
///
/// Measured at `aeb1f4c0`, cache off: all nine `_cx` fixtures below came back
/// `Verified` on bodies that ALWAYS divide by zero — a destructuring `let`, a
/// struct-pattern `let`, a `match` arm, a closure parameter, a `for` pattern,
/// and the FIELD/tuple twins of the same shapes. FIVE of the nine are on the
/// `Expr::Path` route, so this was ROUND 5's blind spot for three rounds, not
/// only round 7's.
#[test]
fn zt1_zt9_every_binder_form_is_a_shadow() {
    for func in [
        "zt1_path_tuple_pat_shadow_cx",
        "zt2_field_tuple_pat_shadow_cx",
        "zt3_struct_tuple_pat_shadow_cx",
        "zt4_path_match_binding_shadow_cx",
        "zt5_field_match_binding_shadow_cx",
        "zt6_path_closure_param_shadow_cx",
        "zt7_path_for_binding_shadow_cx",
        "zt8_field_nested_tuple_pat_shadow_cx",
        "zt9_path_struct_pat_shadow_cx",
    ] {
        assert_not_verified(func);
        assert_sink_does_not_weaken(func, "d6_p2_no_sink_twin");
    }
    // THE DECISIVE CONTROLS. The identical body with the shadowed parameter
    // RENAMED, or DELETED, was a non-verify at `aeb1f4c0` — so what bought the
    // skip was the NAME of an otherwise unused parameter, and these two must
    // stay non-verifies or the pin above would be measuring the body instead.
    assert_not_verified("zt1b_path_tuple_pat_control_renamed_cx");
    assert_not_verified("zt1c_path_tuple_pat_control_no_param_cx");
}

/// THE LIAR TWIN for the round-8 guard, and what keeps it from being satisfiable
/// by recording every name in the body. A destructuring `let` or a `match` arm
/// that binds SOME OTHER name must leave the spec receiver alone: it is still
/// legitimately skipped, because a spec closure carries no panic-freedom
/// obligation (`a6`). All three bodies below are the SAME always-panicking body
/// the `_cx` fixtures use, so only the NAME distinguishes them.
#[test]
fn zt14_zt16_the_guard_discriminates_the_name_not_the_binder() {
    assert_verified("zt14_destructuring_binder_other_name_ok");
    assert_verified("zt15_match_binder_other_name_ok");
    assert_verified("zt16_field_destructuring_binder_other_name_ok");
    // and the round-7 recoveries the round-8 guard must not touch.
    assert_verified("zzs5_unshadowed_ghost_tuple_ok");
    assert_verified("p7_struct_field_ghost_seq_ok");
    assert_verified("x3_struct_field_ghost_seq_exec_elem_ok");
}

/// WHAT THE ROUND-8 GUARD COSTS, measured rather than assumed — and unlike
/// round 7's it is NOT nothing. The collector is FLAT, so a closure parameter or
/// a `for` binding that happens to share the RECEIVER's name now fails closed
/// even though it shadows only inside its own scope. `s.map(|s| s + 1)` is an
/// honest spec body and it verified at `aeb1f4c0`; it does not any more.
///
/// This is the acceptable half of the trade (a fail-closed over-rejection, never
/// the reverse), and separating it would need real scope tracking rather than a
/// flat name set. These two are the signal to re-key if a future round scopes
/// the map.
#[test]
fn zt17_zt18_what_the_flat_binder_set_costs() {
    assert_not_verified("zt17_closure_param_shares_receiver_name");
    assert_not_verified("zt18_for_binding_shares_receiver_name");
}

/// TWO MORE ROUTES PROBED UNDER THE SAME REVIEW, kept as RATCHETS rather than
/// offered as evidence, because each already fails closed for a reason that is
/// not this guard.
///
///   * `zt10`/`zt11` — a nested `fn` item's parameters shadow nothing today
///     because extraction REFUSES a nested `fn` item outright ("Unsupported
///     nested fn item in function body"). If that support ever lands, the flat
///     scan gets this hole immediately and these two fire first.
///   * `zt12`/`zt13` — the FOLD accumulator's mint (`exec_scalar_sort_of_expr`)
///     read the parameter's declared type for a name the body rebinds, so a
///     `u8` shadow of a `u64` parameter was minted at `u64`. Once `acc + 200u8`
///     was typed from both operands, that decided the add at `u64` and both
///     VERIFIED. A name any binder in the body rebinds now gets no accumulator
///     sort, so both fail closed (the obligation over `acc` does not lower).
///     `zt12c_zt12e` pins that the rule is keyed on the rebinding.
#[test]
fn zt10_zt13_routes_probed_that_did_not_weaken() {
    for func in [
        "zt10_path_nested_fn_param_shadow_cx",
        "zt11_field_nested_fn_param_shadow_cx",
        "zt12_fold_accum_ident_shadow_cx",
        "zt13_fold_accum_destructure_shadow_cx",
    ] {
        assert_not_verified(func);
    }
}

/// The controls for the fold-accumulator rebinding rule. A parameter seed
/// that no binder rebinds still mints the accumulator at the parameter's type:
/// the `u8` overflow is refuted and the honest twin verifies, so the rule is
/// not a blanket refusal of name seeds. `zt12e` is its disclosed cost: the scan
/// is flat, so a rebinding in a disjoint block also withholds the mint, and a
/// body that was refuted is now refused. That is a fail-closed loss, never a
/// verify.
#[test]
fn zt12c_zt12e_the_accumulator_rule_is_keyed_on_a_rebinding() {
    assert_counterexample("zt12c_fold_accum_param_seed_cx");
    assert_verified("zt12d_fold_accum_param_seed_ok");
    assert_not_verified("zt12e_fold_accum_shadow_in_other_scope_cx");
}

/// ROUND 9: THE FLAT `let` MAP SPOKE FOR A NAME THE CONTEXT DECLARES.
///
/// Round 5's shadow rule fires only on a DISAGREEMENT between the declared sort
/// and the recorded `let` sort; when the declared sort is `Unresolved` it
/// deliberately lets the `let` answer, on the reading "the context knows
/// nothing, so the `let` must be the binding". A DECLARED parameter reads
/// `Unresolved` too, whenever its collection is reached through a TYPE ALIAS
/// (round 7's `z5c`) — and the scan is FLAT over the whole body, so ANY `let`
/// of that name, in ANY scope and at ANY position, supplied a POSITIVE ghost
/// reading for an exec parameter. Measured at `16240019`, cache off, all seven
/// `Verified` on a body that ALWAYS divides by zero.
#[test]
fn zu1_zu7_a_let_in_another_scope_is_not_this_receiver() {
    for func in [
        "zu1_alias_param_block_scope_ghost_let_cx",
        "zu2_alias_param_closure_scope_ghost_let_cx",
        "zu3_alias_param_match_arm_ghost_let_cx",
        "zu4_alias_param_later_ghost_let_cx",
        "zu5_alias_param_adapter_ghost_let_cx",
        "zu6_alias_param_for_body_ghost_let_cx",
        "zu7_alias_param_unannotated_ghost_let_cx",
    ] {
        assert_not_verified(func);
        assert_sink_does_not_weaken(func, "d6_p2_no_sink_twin");
    }
    // THE DECISIVE CONTROLS. The identical body with the inner `let` RENAMED,
    // and with the inner block DELETED, were non-verifies at `16240019` — so
    // the skip was bought by an UNRELATED statement in a scope the receiver is
    // not in, which is the campaign's blocker pattern.
    assert_not_verified("zu1b_alias_param_control_inner_let_renamed_cx");
    assert_not_verified("zu1c_alias_param_control_no_inner_let_cx");
}

/// THE LIAR TWIN for the round-9 guard. It is trivially satisfiable by
/// silencing the `let` map altogether, which would retire round 6's body-local
/// recovery — so a TRUE BODY LOCAL, a name the context declares nothing for,
/// must still be classified by its own `let`. ONE body, ONE element width, TWO
/// spellings, and the exec half must REFUTE rather than merely not verify.
#[test]
fn zu8_the_let_map_still_speaks_for_a_true_body_local() {
    assert_verified("zu8_body_local_ghost_let_ok");
    assert_counterexample("zu8b_body_local_exec_let_cx");
}

/// ROUND 9: AN `@` PATTERN BINDS MORE THAN ITS HEAD. `local_ident` answers for
/// `Pat::Ident`'s own name and drops the SUBPATTERN, so `let q @ (v, _z) = p;`
/// took the CLASSIFIABLE half as `q` and round 8's opaque half — the only thing
/// that records the other binders — never ran. Measured `Verified` at
/// `16240019` on a body that always divides by zero, with the parameter-renamed
/// control a non-verify.
#[test]
fn zu9_an_at_pattern_binds_more_than_its_head() {
    assert_not_verified("zu9_at_subpattern_shadow_cx");
    assert_sink_does_not_weaken("zu9_at_subpattern_shadow_cx", "d6_p2_no_sink_twin");
    assert_not_verified("zu9b_at_subpattern_control_renamed_cx");
    // THE LIAR TWIN: a subpattern binding SOME OTHER name must leave the spec
    // receiver alone. Only the NAME may distinguish it from `zu9`.
    assert_verified("zu10_at_subpattern_other_name_ok");
    // and the round-7/8 recoveries neither round-9 guard may touch.
    assert_verified("zzs5_unshadowed_ghost_tuple_ok");
    assert_verified("p7_struct_field_ghost_seq_ok");
    assert_verified("x3_struct_field_ghost_seq_exec_elem_ok");
    assert_counterexample("x3b_exec_vec_u64_field_same_body_cx");
}

/// WHAT THE `@` HALF COSTS, measured rather than assumed: the binder set is
/// flat, so a subpattern that merely SHARES the receiver's name fails closed
/// although it shadows only its own scope. Same class and same direction as
/// `zt17`/`zt18`, and the signal to re-key if a future round scopes the map.
#[test]
fn zu11_what_the_at_pattern_half_costs() {
    assert_not_verified("zu11_at_subpattern_shares_receiver_name");
}
