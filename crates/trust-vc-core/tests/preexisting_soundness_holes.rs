// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS PINS for pre-existing holes (false `Verified` on programs that
//! panic or assert-fail at runtime), one section per closed cluster. Every
//! LIAR below was a HEAD `Verified`; its runtime truth was measured by
//! compiling the same body with stock rustc (debug, overflow checks on) and
//! running it on the named witness input. A CONTROL is a runtime-true
//! neighbour the narrow fix keeps `Verified`; a GATED case is a runtime-true
//! neighbour that the fix now fails closed on, pinned with its precise
//! refusal text (a recorded completeness cost, never a counterexample).
//!
//! # Cluster 26/27 — missing arithmetic-safety obligations (2026-09-15)
//!
//! (26) The RHS of an assignment whose left-hand side is not a bare identifier
//! — a field (`s.f = s.f - n`), tuple field (`p.0 = n + 1u8`), index
//! (`a[0usize] = n + 1u8`) or `_` (`_ = 100u8 / n`) — carried no
//! overflow / divide-by-zero / shift / index-read obligation; only the
//! identifier branch of `assign_expr` emitted one. A field / tuple-field
//! COMPOUND assignment (`s.f += n`, `p.1 -= n`, `s.g <<= n`, `s.f ^= 100u8 / n`)
//! emitted nothing either. (27) The scrutinee of `if let P = e` /
//! `while let P = e` (`if let Some(v) = a.get(i + 1usize)`) was only rendered,
//! never checked.
//!
//! Fix (OBLIGATION): `assign_expr` runs the identifier branch's emitters on the
//! RHS of every non-identifier LHS before the sub-path dispatch;
//! `visit_expr_binary` pins the implicit `(place) OP (rhs)` of a projected
//! compound write; `visit_expr_if` / `visit_expr_while` pin the `let`
//! scrutinee at the pre-branch / pre-loop point, as the boolean condition and
//! the `match` scrutinee already were.
//!
//! Fix (HAVOC, found while pinning 26): a projected compound write was also
//! DROPPED from the state — `s.f += 1u8; assert!(s.f == 0u8)` verified, and a
//! second `s.f += 1u8` was checked against the stale value. The place's root
//! binding is now havocked (declared -> fresh symbol, otherwise invalidated so
//! a later read fails closed as `unresolved variable`); a place rooted at a
//! temporary tuple / struct / array literal needs nothing; any other root (a
//! call, method call, dereference, ...) is refused with
//! `compound assignment to a projected place whose root is not a local binding
//! or a temporary literal is unsupported`.
//!
//! Recorded costs of the cluster 26/27 fix (runtime-true, HEAD `Verified`):
//! the four GATED cases below, plus loop-body sites that now render over the
//! loop's havoc symbols exactly as the identifier branch and the boolean `if`
//! condition already did (a Verus-style incompleteness counterexample when a
//! loop-modified operand has no bounding invariant).
//!
//! 46 cases: 26 liars, 16 controls, 4 gated.
//!
//! # Cluster rank 2 — invalidation leaves the BARE name (2026-09-15)
//!
//! `invalidate_scoped` drops a name from every scope frame, after which a read
//! resolves to the bare name — and the bare name is not "unknown": for a
//! declared parameter it is the requires-pinned ENTRY symbol, for a `let` that
//! shadows a parameter it is that parameter, and a later invariant loop that
//! declares the name captures every earlier copy of it. Members: (4 / 12) a
//! declared name written in a plain / `unsafe` / value block read its entry
//! value after the block; (9) a binary operand after a side-effecting value
//! block read the entry (or shadowed-parameter) symbol; (33) a method call on
//! a declared scalar receiver reverted it (`n = 5u64; n.count_ones(); n`,
//! `x.add_assign(1u64)`); (34) a copy of an invalidated local was captured by a
//! later loop declaration; (35) a contract-less helper's body axiom was built
//! from a reverted parameter. Siblings found while pinning, same mechanism: a
//! method call inside a block / `if` / `match` / loop body / closure body (the
//! region restore undid the effect, and the loop frame pinned the receiver),
//! a closure assigning a captured `mut` parameter, and a classified-pure
//! getter on a struct parameter whose field was rewritten.
//!
//! Fix (REFUSE-shaped poison): `invalidate_to_poison` runs the same clean-up
//! and then binds the name, in the frame of its nearest binding, to a symbol
//! that is never declared, so every later read fails closed (an `unresolved
//! variable` error that names the source variable, plus a note). Used at: a
//! plain / `unsafe` block exit (except a name that resolves to its own
//! DECLARED bare symbol at the block's end — the post-state symbol of an
//! invariant loop inside the block, as in the flat `for` / guard-block `while`
//! desugars); exec value-lane side effects (binary operands, call and method
//! arguments / receivers, struct and `vec!` fields — not spec macros, whose
//! "mutating" method names are pure ghost operations); a closure's mutated
//! captures, except a declared binding or a scoped scalar local, which is
//! havocked to a fresh value of its type (the `&mut` call-argument model, so
//! `l2_closure_assign_param` is refuted, not refused); and an unframed method
//! receiver (poisoned unless it is an immutable by-value parameter spelled
//! with a primitive / math scalar type;
//! a registry-classified receiver only when it is declared and rebound).
//! Receiver poisons are re-applied after a block / `if` / `match` / closure
//! restore; a loop body that poisons an outer receiver outside its modified
//! set is refused (`... inside a loop body may change it, and the loop frame
//! does not havoc a method receiver`). A definitional body-axiom render that
//! reads a poison declines (the helper axiom is dropped). No exact modeling.
//!
//! 49 cases: 31 liars, 13 controls, 5 gated (runtime-true, HEAD `Verified`,
//! now fail-closed errors). All 31 liars and 5 gated cases were `Verified`
//! at HEAD; all 31 liars panic in a stock rustc build (overflow checks on) on
//! the witness inputs in each comment's fixture; controls and gated cases run
//! clean.
//!
//! # Cluster rank 3 — value-lane block evaluation drops statement effects (2026-09-15)
//!
//! The value lane (`eval_scoped_stmts`, the scoped rendering of a block in a
//! `let` initializer, an `if` / `match` arm, a return tail or an assertion
//! argument) models only assignment / compound-assignment statements and the
//! recognized collection mutators, and discards its scope when it leaves the
//! block. Every other statement effect was DROPPED and a later read in the same
//! computation saw the pre-effect value. Members: (0) a function-local macro
//! whose transcriber ends in a semicolon-less `if` / `while` / `match` (it was
//! evaluated as a discarded tail); (1) a `let` initializer that writes an outer
//! binding; (8 / 18) a write in a value `if` condition / `match` scrutinee /
//! index base, rendered and rolled back before the branches / arms / index;
//! (10) `let _w = (x = 1u64)`, `let _w = x += 1u64`, `u = (x = 1u64)`; (11) a
//! write inside an `assert!` / `assert_eq!` argument; (13 / 19) a spec
//! assertion nested in an assertion argument, which is only rendered and never
//! emitted; (20) a return-lane tail block with a non-tail join or a writing
//! `let`; (35) `add_assign` autoref through a projected receiver
//! (`self.a.add_assign(1u64)` in a value block / assertion argument / plainly).
//! Siblings found while pinning, same mechanism: a non-tail `while` / `loop` /
//! `if let` / nested block, a closure call, a `vec!` element, an assignment RHS
//! block writing another binding, a `&mut` borrow passed to a call, a method
//! statement or method `let` on a `mut` receiver; a projected receiver whose
//! root is a let-local struct or tuple (`havoc_struct_receiver` havocs only a
//! DECLARED `Datatype` and silently did nothing), including inside an `if`;
//! a write in an assertion argument's block before later statements, inside an
//! `if` or a loop body; a contract-less helper whose value block joins a write.
//!
//! Fix (REFUSE-shaped poison, no new modeling): a SYNTACTIC, positive scan
//! (`ValueLaneEffectScanner`) finds what a value rendering drops — assignment
//! place roots, `&mut` referents, possibly-mutating method receivers (by the
//! same receiver-kind registries and pure-name lists as the obligation lane),
//! `&mut` bindings passed to a writing callee, and the arguments of macros —
//! excluding names bound inside the scanned expression. In `eval_scoped_stmts`
//! each `let` initializer, assignment RHS, compound assignment, non-tail
//! semicolon-less statement, discarded expression statement and spec macro
//! statement is scanned after it is rendered and its written bindings are
//! POISONED (`invalidate_to_poison`, value-lane frames only); a local macro's
//! last statement is no longer a value tail. A value `if` condition / `match`
//! scrutinee / index base with effects renders the rest in a temporary scope
//! over the poison (a declined render refuses instead of reaching the
//! raw-token fallback). An effect no binding names refuses (`a side effect
//! inside a value-position block or expression that vc_extraction cannot
//! attribute to a local binding ...`; a write through a dereference of anything
//! but a scalar `&mut` parameter keeps the pre-existing deref-assignment text).
//! A spec assertion nested in an `assert!` / `assume!` / `assert_eq!` /
//! `invariant!` / ... argument is refused (`a spec assertion nested inside an
//! assertion argument is never emitted as an obligation`). In the obligation
//! lane, a write inside a block of an assertion argument, and a projected
//! method receiver no havoc branch framed, poison their binding and log it for
//! region re-poisoning (a loop body then refuses with the rank-2 loop text); a
//! name bound nowhere (a definitional render's `self`) is poisoned too and
//! re-poisoned after a region.
//!
//! Recorded costs (runtime-true, HEAD `Verified`, now fail-closed errors): the
//! GATED cases below — a value block that joins a write and then reads it under
//! a true bound, and a projected method that is not on the pure-name list
//! (`count_ones`) on a let-local struct / tuple (a declared struct parameter
//! already paid this through `havoc_struct_receiver`).
//!
//! 72 cases: 55 liars, 14 controls, 3 gated. All 72 were `Verified` at git HEAD
//! and at the rank-2 tree; every liar panics in a stock rustc build (overflow
//! checks on) on the witness inputs in its comment, and every control and gated
//! case runs clean on every witness combination.

//!
//! # Cluster rank 4 — the frame collector is blind to closure-captured writes and to pure-name shadows (2026-09-15)
//!
//! `ExternalAssignmentCollector`, which lists the names an `if` / `match` join,
//! a plain / `unsafe` block exit, a loop frame and the value lane treat as
//! written, does not look inside a closure and classifies method calls on
//! collection / scalar / unresolved receivers by method NAME. Members: (3 / 16 /
//! 17) a value block or IIFE writing a plain local; (5) `x.add_assign(9u64)` in
//! a then / else / match arm / loop / invariant loop / closure / plain block;
//! (14) a user `&mut self` trait method on `u64`; (35 / o1-o3) `Option::take` /
//! `replace` and autoref on projected receivers; (c05k) the same on a `mut`
//! parameter. The autoref and method-receiver members were already closed by
//! the rank-2 / rank-3 receiver poison (a region re-poisons a logged receiver,
//! a loop body refuses one); they are pinned here so the cluster stays closed.
//!
//! What was still open at the rank-3 tree, all `Verified` at git HEAD:
//! (a) a CLOSURE that writes a capture inside a region or a loop body —
//! `if b { (|| { v = 3u64; })(); } assert!(v == 0u64)`, the else / match arm /
//! match guard / plain / `unsafe` / value-`if` / value-block twins, a closure
//! bound or passed to a call in the branch, a nested closure, a field of a
//! captured struct, a `mut` parameter, a return tail, and every loop shape.
//! The closure visit poisoned the capture, but the region's scope restore
//! undid the poison and the collector never listed the capture. (b) the
//! PURE-NAME SHADOW, the collection twin of member 14: Rust method
//! resolution tries a receiver type's `&mut` autoref step before
//! auto-dereferencing, so `impl Grab for Vec<u64> { fn get(&mut self, ..) }`
//! makes `v.get(0usize)` a write, while vc_extraction framed `get` (and
//! `contains`, `first`, `count`, `len`, ...) as a pure read by name — in the
//! straight line, in a branch, in a loop and in a value block; likewise for a
//! blanket `impl<T: Tick4> Peek4 for T` on a struct (the receiver-kind registry
//! keys that impl by `T`, not by the struct) and `impl Cnt4 for [u64; 2]`.
//! (c) the TYPED `&mut` RECEIVER, found while pinning (b): the receiver-kind
//! registry reads only the `&mut self` shorthand, so `fn bump(self: &mut
//! Self)` was recorded as by-value (pure) and `r.bump(); assert!(r.x ==
//! 0u64)` verified — straight line, branch and loop.
//!
//! Fix (REFUSE-shaped, no modeling): (a) the closure visit LOGS each written
//! capture it poisons (`poison_and_log_effect_root`), so the region restores
//! re-poison it exactly like a method receiver, and a loop body whose closure
//! writes an outer name outside the loop's modified set is refused (`a closure
//! inside a loop body writes the captured `v`, and the loop frame does not
//! havoc a closure capture`). (b) the file's trait impls for NON-ADT self types
//! (`super::file_non_adt_mut_self_method_impls`) name the `&mut`-receiver
//! methods that can shadow a pure read; a method call with such a name that is
//! on a pure-name list is refused at the obligation lane's method-call
//! chokepoint (`a call to `.get(..)` may resolve to the `&mut self` method
//! ...`) unless the receiver's struct type resolves and the registry records
//! that `(type, method)` pair — the type-keyed escape. (c) a call to a method
//! the file declares with a typed `&mut` receiver is refused at the same
//! chokepoint with no escape (`... with a typed `&mut` receiver, which the
//! receiver-kind registry does not classify as mutating`). The value-lane
//! scanner treats a (b) / (c) call as an effect.
//!
//! Recorded costs (runtime-true, HEAD `Verified`, now fail-closed errors): the
//! GATED cases — a `move` closure, a closure writing the value the capture
//! already holds (in a branch and in a loop), a `&mut self` shadow that writes
//! nothing, and a typed `&mut` receiver method that writes nothing.
//!
//! Corpus: the extraction A/B over every function of `evals/verus/ported`, and
//! over every `fn` literal of the `trust-vc-core` / `trust-vc` test suites,
//! changed NO record against the rank-3 tree except this section's own fixture.
//!
//! 50 cases: 39 liars, 6 controls, 5 gated. All 50 were `Verified` at git HEAD
//! (HEAD sources swapped in, `SRC_C4` as written); every liar panics in a stock rustc
//! build (overflow checks on) on the witness input in its comment, and every
//! control and gated case runs clean on every witness combination.
//!
//! # Cluster rank 5 — integer literal width lost (2026-09-15)
//!
//! (32) An unsuffixed integer literal ASSIGNED to a typed binding stayed
//! untyped: `let mut x: u8 = 0u8; x = 250; x = x + 10;` rendered `x` as the
//! bare `250`, which re-lowers at the `i32` placeholder, so `x + 10` was
//! checked at 32 bits and verified (also `*r = 250;`, a `mut` parameter,
//! deferred init, a block, a loop body, `x = 0; x = x - 1;`, a `<<`). The
//! `let x: u8 = 250;` initializer had the `#2778` suffixing; a negative
//! (`let x: i8 = -128;`) or composite (`let x: u8 = 200 + 50;`) initializer
//! did not. (31) An explicit `21i32` lowers to the same `Int { width: 32 }` as
//! an unsuffixed literal, and `encode_int_lit` narrows such a literal to the
//! most common variable width: next to an `i8` variable `21i32 * 21i32` was
//! computed — and wrapped — at BV8 while the constant-fold overflow verdict
//! was taken at 32 bits, so `r0 != 441i32` verified (also `100i32 + 100i32`,
//! `-(..)`, `-128i32 / -1i32`, operands substituted from `let`s, and the
//! unsuffixed `21 * 21` whose Rust type is `i32`).
//!
//! Fix (a), extraction: `super::single_typed_int_bindings` names the bindings
//! bound EXACTLY ONCE across the signature and every body pattern whose one
//! binding spells a primitive integer type (`x: u8`, `let x: u8`, or
//! `let x = 5u8`). A bare literal assigned to one (`x = 250;`, `*r = 250;`,
//! `x = -128;`) is rendered with that type as its suffix — the `let`
//! mechanism reused verbatim, which also now covers a negative `let`
//! initializer. A COMPOSITE literal value (`200 + 50`, `if b { 1 } else { 0 }`,
//! `{ 250 }`) written to such a binding or to an annotated `let` is refused:
//! `an unsuffixed integer literal value written to a `u8` binding is
//! unsupported in vc_extraction unless it is a single literal`. A name bound
//! more than once keeps the untyped rendering (control `c5_untyped_shadow_of_u8_param`).
//! Fix (b), encoder: a CLOSED default-width literal operation (every leaf an
//! `Int { width: 32 }` literal, joined by `+ - * / % & | ^` / unary `-`) is
//! encoded with context narrowing suppressed for its operands, so it is
//! computed at its IR width; every other operand shape is unchanged.
//!
//! Recorded costs (runtime-true, HEAD `Verified`, now fail-closed errors): the
//! GATED cases — a composite literal value assigned or `let`-bound to a typed
//! binding. Corpus: the extraction A/B over every function of
//! `evals/verus/ported` changed NO record against the rank-4 tree; a verdict
//! sweep over every non-`impl` ported function (2834) with the encoder change
//! instrumented recorded ZERO closed-literal operations encoded under a
//! narrower context width, i.e. (b) changes no ported verdict. Over the test
//! suites' `fn` literals only three `mode_spec_context_diagnostics` fixtures
//! changed (`x = 6;` on a `u64` now renders `6u64`); their pins still hold.
//!
//! 38 cases: 26 liars, 9 controls, 3 gated. All 38 were `Verified` at git HEAD
//! (HEAD sources swapped in, `SRC_C5` as written); every liar panics in a stock
//! rustc build (overflow checks on, `arithmetic_overflow` allowed) on its
//! witness, and every control and gated case runs clean on every witness.
//!
//! # Cluster rank 6 — `#[cfg]` never evaluated (2026-09-15)
//!
//! vc_extraction evaluates no `cfg` predicate. (7) A cfg-gated STATEMENT was
//! modeled as running: `#[cfg(any())] if b { x = 5u64; }`, `#[cfg(any())] let
//! x: u64 = 2u64;` (c07d), a gated `trust_vc::assume!` (consumed as an
//! assumption), a gated `v.push(..)`, a gated `let` that hid an overflow or
//! shadowed a parameter / the return tail. (22) At FILE level the first
//! same-named definition won regardless of `cfg`: `#[cfg(any())] const K: u64 =
//! 1u64; #[cfg(not(any()))] const K: u64 = 2u64;` read `K == 1` in a body, a
//! `requires` and an `ensures`; and two cfg-selected definitions of the VERIFIED
//! function resolved to the compiled-out one.
//!
//! Fix (REFUSE, no modeling; `vc_extraction::refuse_unevaluated_cfg`, run after a
//! successful extraction so every earlier refusal keeps its text): (a) a `cfg` /
//! `cfg_attr` attribute anywhere in the verified function's tokens — its own
//! attributes, signature, body, nested items, macro arguments — fails closed
//! (`a `#[cfg]` / `#[cfg_attr]` attribute in `f` is not evaluated by
//! vc_extraction ...`); (b) with a file, the names the function can REACH (its
//! tokens, then transitively the tokens of every file item whose declared name
//! is reached; a glob `use` / unnamed item macro is always reached) must not
//! include a name DECLARED by an item that carries or contains such an attribute
//! (`K` reaches a declaration in this file that carries a `#[cfg]` ...`). A
//! `cfg_attr` whose attributes are all lint / documentation attributes (`allow`,
//! `doc`, `inline`, ...) is inert. Inside a cfg-gated module every declaration
//! is tainted except a `use` (module-local) and the verified function itself.
//!
//! Recorded costs (runtime-true, HEAD `Verified`, now fail-closed errors): the
//! GATED cases — a live `#[cfg(all())]` statement, an unused gated nested const,
//! the cfg-selected const whose live arm happens to be first, and a root
//! function whose name a `#[cfg(test)] mod tests` redeclares. Corpus: the
//! extraction A/B over every function of `evals/verus/ported` (2967 records) and
//! every `fn` literal of the `trust-vc-core` / `trust-vc` test suites changed NO
//! record against the rank-5 tree outside this section's own fixtures (the three
//! cargo fixtures' `#[cfg(test)] mod tests` are unaffected).
//!
//! 24 cases: 13 liars, 7 controls, 4 gated. All 24 were `Verified` at git HEAD
//! (HEAD sources swapped in, the `SRC_C6*` fixtures as written); every liar
//! panics in a stock rustc build (overflow checks on) on the witness in its
//! comment, and every control and gated case runs clean on every witness.
//!
//! # Review round 1 — regressions of ranks 1 and 5, and nine pre-existing holes (2026-09-15)
//!
//! A review of the six cluster fixes above found two INTRODUCED false
//! `Verified`s, two INTRODUCED false counterexamples, and nine holes that
//! pre-date every fix (HEAD `Verified`). Everything below was re-measured with
//! a git-HEAD build, a build of the rank-6 tree and the final tree.
//!
//! INTRODUCED by rank 5 (closed here, encoder only): the closed-literal
//! narrowing suppression treated `(100 + 100)` as an independent 32-bit value
//! even where Rust types it at a NARROWER peer, so `z + (100 + 100)` with `z:
//! u8` (and the `- * i8 i16 u16` twins, assignment / compound / return-lane /
//! value-`if` / loop-body / nested / left-operand / spec forms) was computed and
//! overflow-checked at 32 bits, and `y == 100 + 100` with `y: i8` could never
//! be equal. Fix: the suppression is cancelled inside any operand whose context
//! type is a bounded integer narrower than 32 bits
//! (`narrow_typed_literal_operand_context`), and `coerce_default_int_literal`
//! retypes a CLOSED literal tree the way it already retyped a lone literal —
//! which also closes the pre-existing `a[0usize] + (100 + 100)`, `(z as u8) +
//! (100 + 100)`, `z + (0xF0 & 0xFF)` and `y != 200 + 100` (u8) forms. Every
//! rank-5 liar and control keeps its verdict.
//!
//! INTRODUCED by rank 1, F1 (closed here): a projected compound (`s.f += n`)
//! HAVOCKED the whole declared root to a fresh symbol, so a runtime-true claim
//! about any other part of the binding (a sibling field, an untouched tuple
//! field in the postcondition, the same field's next bounded compound) was
//! REFUTED. The root is now POISONED (`invalidate_to_poison`, rank 2's move):
//! the same reads are a fail-closed `unresolved variable` error. The two
//! rank-1 liars that were pinned as counterexamples through that havoc are now
//! pinned as fail-closed errors.
//!
//! INTRODUCED by rank 1, F2 (closed here): the three obligation sites rank 1
//! ADDED (a projected-place assignment RHS, an `if let` scrutinee, a `while
//! let` scrutinee) render, inside a loop body, over the loop's fresh havoc
//! symbols, and over a loop-modified operand with no bounding invariant that
//! is a false counterexample on a true loop (`while i < 10u8 { if let 0u8 = x +
//! 1u8 {} x = 1u8; .. }`, `a[i] = last + 1u8`). Such a site is now REFUSED
//! (`refuse_new_site_over_loop_body_havoc`: any arithmetic / index site whose
//! rendering mentions a `__loopbody_` symbol fails closed); a site whose
//! operands are loop-invariant is emitted and refuted exactly as before. The
//! rank-1 control `s.f = i + 1u8` under `i < 10u8` is the one pre-existing pin
//! that moves (Verified -> gated error, `g_loop_field_assign_add`).
//!
//! PRE-EXISTING (HEAD `Verified`), closed here by the narrowest move in code
//! the six fixes already touched:
//! * a compound assignment to a declared name no scope frame binds (a `mut`
//!   parameter, a rebound parameter, a shadowing `let`) fell back to
//!   `invalidate_scoped` and read the ENTRY symbol — now poisoned (loop bodies
//!   keep the loop lane's own invalidate);
//! * an index assignment whose index has a side effect unbound the array to its
//!   bare name — now poisoned;
//! * effects in a `while` condition / `while let` scrutinee (`while let Some(_)
//!   = v.pop() {}`, `while v.pop().is_some() {}`, a receiver / closure / block
//!   write in a condition block) were framed by nothing — the loop is refused
//!   (`the condition of this `while` loop may change `v` ...`);
//! * `push` / collection-mutator arguments and `vec!` elements were only
//!   rendered, so a nested spec assertion or an arithmetic site inside them was
//!   never emitted — they are now visited at the pre-call state;
//! * a by-value `self` of a trait implemented for `&mut T` is a mutable
//!   receiver — recorded by the shadow scan and the receiver-kind registry
//!   (review round 2 re-keyed it to its own kind, `ValueMutRef`, which
//!   poisons instead of havocking; see below);
//! * an impl declared by a `macro_rules!` transcriber / item-macro invocation
//!   was invisible to the shadow scan — every macro token group is re-parsed
//!   (`a macro expansion in this file`);
//! * a shadowed pure method inside an `assert!` argument ran its `&mut self`
//!   write at runtime but was rendered as a pure spec read — refused at the
//!   assertion-argument scan;
//! * `#[r#cfg(..)]` / `#[r#cfg_attr(..)]` (raw-identifier spellings rustc
//!   honours) escaped the rank-6 refusal — the `r#` prefix is stripped before
//!   the name test.
//!
//! STILL OPEN (recorded, not fixed; every one is HEAD `Verified` and
//! runtime-false): unsuffixed literal width outside the scalar `let` /
//! assignment shapes — a `let` whose type comes from a cast (`0 as u8`), an
//! associated const (`u8::MIN`) or a copy (`let mut x = y`), and a name bound
//! twice (`let x: u64; let mut x: u8`) followed by `x = 250; x = x + 10`; the rank-4
//! helper-axiom typed-`&mut`-receiver liar; and the rank-4 loop copy-capture of
//! a projected read. Two shapes deliberately keep HEAD's handling so that no
//! corpus pin moves: a collection-mutator call with a `&mut` argument
//! (`v1.append(&mut v2)`) is not pre-visited, so a nested obligation inside
//! such an argument stays unemitted there, and an UNTRACKED (alias-rooted)
//! effect in a `while` condition (`while cond(value_ref)`) is left to the
//! mut-ref lane, which the `mut_refs_loops` port pins as `unresolved variable
//! `value``. Also recorded: the `use std::ops::AddAssign` import the
//! `add_assign` fixtures need at runtime is part of the fixture text.
//!
//! CLOSED 2026-09-18 by the `let` ANNOTATION WIDTH CARRY
//! (`vc_extraction::declared_width`, pinned by
//! `tests/let_annotation_width_capability.rs`): exactly ONE of the five shapes
//! above — the typed array literal `let a: [u8; 1] = [250]; a[0] + 10` — is
//! now refuted, together with every other COMPOSITE `let` ascription
//! (`Option<uN>`, `Vec<uN>`, `[uN; k]` in both forms, tuples and their
//! destructuring, `&uN`, `&[uN]`, `core::primitive::uN`, file-local `type`
//! aliases of any of those, and the DEFERRED `let x: T; x = ..;` form). The
//! other four stay open and stay listed: they are the H1b BACKWARD-inference
//! class, where the literal has no ascription at its own binding at all.
//!
//! NEW RESIDUALS recorded by that increment, neither claimed closed nor
//! silently dropped: (1) with no `syn::File` the file name table cannot be
//! built, so the carry is OFF and today's rendering stands; (2) a
//! definitional / sibling render (`CollectorLaneSeed::EMPTY`) carries an empty
//! shape map, so only the DEFERRED-assignment half is off there — the
//! `let`-initializer half reads the local's own pattern and still applies; and
//! (3) FLOATS are not carried, on a measurement: a suffixed `f32` literal in a
//! composite comes back `Incompleteness` rather than a refutation, so
//! re-spelling the bare form would buy a fail-closed `Unknown` instead of a
//! counterexample. `let v: Vec<f32> = vec![16777216.0]; v[0] + 1.0 > v[0]`
//! stays HEAD `Verified` and runtime-false. (4) A GLOB import — at FILE scope
//! or inside a function body — turns the composite carry off for every
//! width-bearing primitive spelling in that file, because a glob really can
//! rebind a primitive type NAME (measured: `mod m { pub type u64 = i32; }
//! use m::*;` makes `size_of::<u64>()` four) and can rebind `core` itself
//! (measured: a glob-imported `m::core` makes `core::primitive::u8` eight
//! bytes wide while `::core::primitive::u8` in the same file stays one). So
//! `let v: Vec<u8> = vec![200]` stays HEAD `Verified` in a glob-bearing file,
//! and the capture-proof spelling is the LEADING-`::` `::core::primitive::uN`,
//! NOT the unqualified `core::primitive::uN` this list first named. How far
//! that reaches was RE-MEASURED 2026-09-18 and is much smaller than first
//! recorded: 5 of the 167 `evals/verus/ported` files carry any glob, exactly 1
//! mentions `vstd::prelude` (the earlier "every ported corpus file writes
//! `use vstd::prelude::*;`" was simply false), and 0 corpus sites hold the
//! shape this lane can reach. (5) A name an inline `mod` of the file rebinds is
//! undecided in BOTH directions — the table is file-scope and the extraction
//! is handed no module path — so such a `let` REFUSES rather than resolving to
//! either meaning. (5b) The same for a name bound by a `use` written INSIDE a
//! function body or a nested block, at any depth: that is the ordinary way a
//! multi-file crate imports a type, it shadows for the rest of the body only,
//! and a FILE-scope table can represent neither fact. Measured as a false
//! `Verified` on a panicking program (`type W = u64;` + a body
//! `use other::W;` where the import is a `u32`). (5c) A
//! `core::primitive::uN` whose `core` prefix the file captures — `mod core`,
//! `use m as core;`, or a body-scope rename — is undecided for the same
//! reason; all three were measured false `Verified`s. (6) A bare literal beside a NON-CONSTANT operand
//! (`let z = 200; let v: Vec<u8> = vec![z + 50];`) is refused, not carried:
//! this file alone cannot show the `+` is the primitive impl. That refusal is
//! load-bearing — the same body is a HEAD false `Verified` on a program that
//! panics — and it costs the true-claim spelling (`let z = 50u8;`) with it.
//!
//! 111 cases: 82 liars, 15 controls, 14 gated (7 F1, 5 F2, 2 state-lane); the
//! three rank-1 pins this round moves (`l_param_tuple_compound_then_stale_read`,
//! `l_param_struct_compound_then_stale_read`, `g_loop_field_assign_add`) stay
//! in the rank-1 section. Every liar was `Verified` at git HEAD except the 24
//! rank-5-regression liars (`Verified` at the rank-6 tree, refuted at HEAD and
//! again now) and `lr_while_cond_block_assign_local` (refuted at HEAD, kept as
//! the plain-assignment twin of the refused shapes). Every liar panics in a
//! stock rustc build (overflow checks on) on the witness in its comment, and
//! every control and gated case runs clean on every witness.
//!
//! # Review round 2 — two regressions of review round 1 (2026-09-15)
//!
//! INTRODUCED by round 1's `vec!` / mutator-argument visiting (closed here):
//! the elements of an exec `vec!` and a block / value-`if` / `match`
//! argument of a collection-mutator call were visited through the statement
//! lane, which inside a loop body renders an arithmetic site over the loop's
//! fresh havoc symbols — the F2 shape again, at two sites F2's refusal did
//! not guard, so `while i < 10u8 { let w: Vec<u8> = vec![x + 1u8]; x = 1u8;
//! .. }` and `v.push({ x + 1u8 })` (twelve runtime-true probes) were REFUTED
//! where HEAD verified. Fix: the same refusal, applied to every `vec!`
//! element (`refuse_vec_element_over_loop_body_havoc`) and, for a mutator
//! argument, to exactly the sites the pre-visit ADDS — those nested under a
//! node the value-position collector does not enter
//! (`refuse_mutator_argument_over_loop_body_havoc`), so a plain `v.push(x +
//! 1u8)` keeps HEAD's statement-lane verdict byte for byte. The arithmetic
//! sites are now collected at any depth for the rank-1 sites too, so a block
//! scrutinee is refused as well. Index reads are not scanned at these two
//! sites: no index bound is ever emitted inside a loop body, so they cannot
//! be a new obligation, and `vec![a[i]]` over the guard var keeps verifying.
//! Cost, recorded: a guard-bounded / `for`-var / invariant-first operand at
//! these sites (HEAD Verified) is now the same fail-closed error as the rank-1
//! `s.f = i + 1u8` control — the refusal is name-based.
//!
//! INTRODUCED by round 1's by-value `&mut T` receiver classification (closed
//! here): `impl<'a> PeekRef for &'a mut S4 { fn peek(self) }` was registered
//! as `RefMut`, which routed `s.peek()` to the whole-struct HAVOC, so a
//! runtime-true claim about an untouched field, the result or a
//! postcondition (`s.peek(); assert!(s.a == 5u64)`, ten probes) was REFUTED
//! where HEAD verified. Fix: the kind is its own `SelfReceiverKind::ValueMutRef`;
//! the straight-line and projected receiver paths POISON the root (F1's move),
//! the loop / branch modified-set collector leaves it out so the region exit
//! re-poisons (a branch / `match` / block) or refuses the loop (`a method
//! call on `s` inside a loop body may change it`), and every fail-closed
//! classification (the value-lane scanner, the `&mut`-struct postcondition
//! reject) still counts it as a mutation. The round-1 liar
//! `lr_refmut_by_value_count_param` moves from a counterexample to the same
//! fail-closed error.
//!
//! 70 cases: 18 + 17 gated, 10 + 12 liars, 9 + 4 controls. Every gated case
//! and control runs clean in a stock rustc build (overflow checks on) on every
//! witness; every liar panics or returns the wrong value on its witness.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_pesh_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

fn expect_verified(func: &str) {
    match verify(func, func, SRC_C26) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

/// A liar refuted by the new obligation: a Counterexample whose obligation
/// names the panic class.
fn expect_counterexample_on(func: &str, fragment: &str) {
    match verify(func, func, SRC_C26) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.contains(fragment) => {}
        other => panic!("{func}: expected a Counterexample naming {fragment:?}, got {other:?}"),
    }
}

/// Fail-closed error containing every needle (a liar or a gated true claim).
fn expect_error_containing(func: &str, needles: &[&str]) {
    match verify(func, func, SRC_C26) {
        VerifyResult::Error { message } if needles.iter().all(|n| message.contains(n)) => {}
        other => {
            panic!("{func}: expected the fail-closed error containing {needles:?}, got {other:?}")
        }
    }
}

const UNRESOLVED: &str = "unresolved variable";
const LOOP_HAVOC_SITE_REFUSAL: &str = "inside a loop body reads a loop-modified binding whose in-loop value this site cannot render exactly";
const PROJECTED_ROOT_REFUSAL: &str = "compound assignment to a projected place whose root is not a local binding or a temporary literal is unsupported";

const SRC_C26: &str = r#"
struct Pl {
    f: u8,
    g: u16,
}

struct W {
    p: Pl,
}

fn get(s: &mut Pl) -> &mut Pl {
    s
}

// ---- 26: non-identifier-LHS plain assignment RHS ----------------------------

// LIAR a2: panics at n = 1 (subtract overflow).
#[trust_vc::ensures(true)]
fn l_field_assign_sub(n: u8) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f = s.f - n;
}

// LIAR c26e: panics at n = 255.
#[trust_vc::ensures(true)]
fn l_tuple_field_assign_add(n: u8) {
    let mut p: (u8, u8) = (0u8, 0u8);
    p.0 = n + 1u8;
}

// LIAR c26c: panics at n = 255 (the compound `a[0usize] += n` was already checked).
#[trust_vc::ensures(true)]
fn l_index_assign_add(n: u8) {
    let mut a: [u8; 2] = [0u8, 0u8];
    a[0usize] = n + 1u8;
}

// LIAR: panics at n = 255 (2-D index write).
#[trust_vc::ensures(true)]
fn l_nested_index_assign_add(n: u8) {
    let mut a = [[0u8; 2]; 2];
    a[0usize][1usize] = n + 1u8;
}

// LIAR c26b: panics at n = 0 (divide by zero).
#[trust_vc::ensures(true)]
fn l_underscore_assign_div(n: u8) {
    _ = 100u8 / n;
}

// LIAR: panics at i = 3 (index read in a field-assignment RHS).
#[trust_vc::ensures(true)]
fn l_field_assign_index_read(i: usize, a: [u8; 3]) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f = a[i];
}

// LIAR: panics at n = 0 (arithmetic nested in a call argument).
#[trust_vc::ensures(true)]
fn l_field_assign_nested_div(n: u8) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f = core::cmp::min(100u8 / n, 3u8);
}

// LIAR: panics at n = 255 (field of an array element).
#[trust_vc::ensures(true)]
fn l_array_element_field_assign_add(n: u8) {
    let mut v = [Pl { f: 0u8, g: 0u16 }, Pl { f: 0u8, g: 0u16 }];
    v[0usize].f = n + 1u8;
}

// LIAR: panics at n = 255 (write through a `&mut` alias field).
#[trust_vc::ensures(true)]
fn l_mut_ref_alias_field_assign_add(n: u8) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    let r = &mut s;
    r.f = n + 1u8;
}

// CONTROL: overflow-safe under the precondition.
#[trust_vc::requires(n < 255u8)]
#[trust_vc::ensures(true)]
fn c_field_assign_add(n: u8) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f = n + 1u8;
}

// CONTROL
#[trust_vc::requires(n < 255u8)]
#[trust_vc::ensures(true)]
fn c_tuple_field_assign_add(n: u8) {
    let mut p: (u8, u8) = (0u8, 0u8);
    p.0 = n + 1u8;
}

// CONTROL
#[trust_vc::requires(n < 255u8)]
#[trust_vc::ensures(true)]
fn c_index_assign_add(n: u8) {
    let mut a: [u8; 2] = [0u8, 0u8];
    a[0usize] = n + 1u8;
}

// CONTROL
#[trust_vc::requires(n > 0u8)]
#[trust_vc::ensures(true)]
fn c_underscore_assign_div(n: u8) {
    _ = 100u8 / n;
}

// CONTROL
#[trust_vc::requires(i < 3usize)]
#[trust_vc::ensures(true)]
fn c_field_assign_index_read(i: usize, a: [u8; 3]) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f = a[i];
}

// GATED (review round 1, F2): a field assignment inside a guarded loop body
// whose RHS reads the loop-modified counter `i`. The rank-1 site rendered it
// over `i__loopbody_N` (Verified here, since the guard bounds `i`, but a
// Counterexample on a true loop wherever the operand is unbounded), so the
// site is now refused whenever an operand resolves to a loop havoc symbol.
#[trust_vc::ensures(true)]
fn g_loop_field_assign_add() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    let mut i = 0u8;
    while i < 10u8 {
        s.f = i + 1u8;
        i += 1u8;
    }
}

// ---- 26: projected compound assignment --------------------------------------

// LIAR c26a: panics at n = 255.
#[trust_vc::ensures(true)]
fn l_field_compound_add(n: u8) {
    let mut s = Pl { f: 1u8, g: 0u16 };
    s.f += n;
}

// LIAR c26d: panics at n = 1.
#[trust_vc::ensures(true)]
fn l_tuple_field_compound_sub(n: u8) {
    let mut p: (u8, u8) = (0u8, 0u8);
    p.1 -= n;
}

// LIAR: panics at n = 16 (shift overflow).
#[trust_vc::ensures(true)]
fn l_field_compound_shl(n: u32) {
    let mut s = Pl { f: 1u8, g: 0u16 };
    s.g <<= n;
}

// LIAR: panics at n = 0 (divide by zero inside a bitwise compound RHS).
#[trust_vc::ensures(true)]
fn l_field_compound_bitxor_div(n: u8) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f ^= 100u8 / n;
}

// LIAR: panics at a = u64::MAX (compound on a temporary tuple literal's field).
#[trust_vc::ensures(true)]
fn l_temporary_tuple_compound_add(a: u64) {
    let b: u64 = 1u64;
    (a, b).0 += 5u64;
}

// CONTROL
#[trust_vc::requires(n < 200u8)]
#[trust_vc::ensures(true)]
fn c_field_compound_add(n: u8) {
    let mut s = Pl { f: 1u8, g: 0u16 };
    s.f += n;
}

// CONTROL
#[trust_vc::requires(n < 200u8)]
#[trust_vc::ensures(true)]
fn c_tuple_field_compound_add(n: u8) {
    let mut p: (u8, u8) = (1u8, 0u8);
    p.1 += n;
}

// CONTROL
#[trust_vc::requires(n < 16u32)]
#[trust_vc::ensures(true)]
fn c_field_compound_shl(n: u32) {
    let mut s = Pl { f: 1u8, g: 0u16 };
    s.g <<= n;
}

// CONTROL
#[trust_vc::requires(n > 0u8)]
#[trust_vc::ensures(true)]
fn c_field_compound_bitxor_div(n: u8) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f ^= 100u8 / n;
}

// CONTROL: a plain field write followed by a compound write reads the written value.
#[trust_vc::ensures(true)]
fn c_field_assign_then_compound() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f = 254u8;
    s.f += 1u8;
}

// CONTROL: the `mut_refs_temporaries` port shape keeps verifying.
#[trust_vc::ensures(true)]
fn c_temporary_tuple_compound_keeps_sources() {
    let mut a: u64 = 1u64;
    let mut b: u64 = 1u64;
    (a, b).0 += 5u64;
    assert!(a == 1u64);
    assert!(b == 1u64);
}

// ---- 26: projected compound write dropped from the state (havoc) ------------

// LIAR: assert fails at runtime (s.f is 1).
#[trust_vc::ensures(true)]
fn l_field_compound_then_stale_read() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f += 1u8;
    assert!(s.f == 0u8);
}

// LIAR: assert fails at runtime.
#[trust_vc::ensures(true)]
fn l_local_tuple_compound_then_stale_read() {
    let mut p = (0u8, 0u8);
    p.0 += 1u8;
    assert!(p.0 == 0u8);
}

// LIAR: assert fails at runtime for p = (0, 0).
#[trust_vc::requires(p.0 == 0u8)]
#[trust_vc::ensures(true)]
fn l_param_tuple_compound_then_stale_read(mut p: (u8, u8)) {
    p.0 += 1u8;
    assert!(p.0 == 0u8);
}

// LIAR: assert fails at runtime for f = 0.
#[trust_vc::requires(s.f == 0u8)]
#[trust_vc::ensures(true)]
fn l_param_struct_compound_then_stale_read(mut s: Pl) {
    s.f += 1u8;
    assert!(s.f == 0u8);
}

// LIAR: assert fails at runtime.
#[trust_vc::ensures(true)]
fn l_nested_field_compound_then_stale_read() {
    let mut w = W { p: Pl { f: 0u8, g: 0u16 } };
    w.p.f += 1u8;
    assert!(w.p.f == 0u8);
}

// LIAR: assert fails at runtime.
#[trust_vc::ensures(true)]
fn l_array_element_field_compound_then_stale_read() {
    let mut v = [Pl { f: 0u8, g: 0u16 }];
    v[0usize].f += 1u8;
    assert!(v[0usize].f == 0u8);
}

// LIAR: the second write panics (254 + 1 + 1); it was checked against 254.
#[trust_vc::ensures(true)]
fn l_field_compound_twice_overflows() {
    let mut s = Pl { f: 254u8, g: 0u16 };
    s.f += 1u8;
    s.f += 1u8;
}

// GATED: runtime-true (253 + 1 + 1), now fails closed on the havocked root.
#[trust_vc::ensures(true)]
fn g_field_compound_twice_safe() {
    let mut s = Pl { f: 253u8, g: 0u16 };
    s.f += 1u8;
    s.f += 1u8;
}

// GATED: runtime-true; the unrelated field read now fails closed.
#[trust_vc::ensures(true)]
fn g_field_compound_then_other_field_read() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    s.f += 1u8;
    assert!(s.g == 0u16);
}

// GATED: runtime-true, refused (call-rooted place).
#[trust_vc::ensures(true)]
fn g_call_rooted_compound() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    get(&mut s).f += 1u8;
}

// ---- 27: if-let / while-let scrutinee ---------------------------------------

// LIAR i1: panics at i = usize::MAX.
#[trust_vc::ensures(true)]
fn l_if_let_scrutinee_index_arith(i: usize, a: [u8; 3]) {
    if let Some(_v) = a.get(i + 1usize) {}
}

// LIAR c27a: panics at n = 255.
#[trust_vc::ensures(true)]
fn l_if_let_scrutinee_add(n: u8) {
    if let 0u8 = n + 1u8 {}
}

// LIAR c27b: panics at n = 0.
#[trust_vc::ensures(true)]
fn l_if_let_scrutinee_nested_div(n: u8) {
    if let Some(_v) = Some(100u8 / n) {}
}

// LIAR c27c: panics at n = 255.
#[trust_vc::ensures(true)]
fn l_while_let_scrutinee_add(n: u8) {
    while let 0u8 = n + 1u8 {
        break;
    }
}

// LIAR: panics at c = false, n = 255 (else-if-let, checked on the reachable path).
#[trust_vc::ensures(true)]
fn l_else_if_let_scrutinee_add(c: bool, n: u8) {
    if c {
    } else if let 0u8 = n + 1u8 {
    }
}

// CONTROL
#[trust_vc::requires(i < 2usize)]
#[trust_vc::ensures(true)]
fn c_if_let_scrutinee_index_arith(i: usize, a: [u8; 3]) {
    if let Some(_v) = a.get(i + 1usize) {}
}

// CONTROL
#[trust_vc::requires(n < 255u8)]
#[trust_vc::ensures(true)]
fn c_while_let_scrutinee_add(n: u8) {
    while let 0u8 = n + 1u8 {
        break;
    }
}

// CONTROL: the else-if-let obligation is guarded by `!c`.
#[trust_vc::requires(c || n < 255u8)]
#[trust_vc::ensures(true)]
fn c_else_if_let_scrutinee_add(c: bool, n: u8) {
    if c {
    } else if let 0u8 = n + 1u8 {
    }
}

// CONTROL: an arithmetic-free if-let is untouched.
#[trust_vc::ensures(true)]
fn c_if_let_plain(o: Option<u8>) {
    if let Some(v) = o {
        assert!(v == v);
    }
}

// GATED: runtime-true; the inner scrutinee reads the outer if-let binding `v`,
// which this lane cannot resolve, so the new obligation fails closed.
#[trust_vc::requires(n < 255u8)]
#[trust_vc::ensures(true)]
fn g_nested_if_let_binding_scrutinee(n: u8) {
    if let Some(v) = Some(n) {
        if let 0u8 = v + 1u8 {}
    }
}
"#;

// ---- 26: non-identifier-LHS plain assignment RHS ----------------------------

#[test]
fn liar_field_assign_sub_is_refuted() {
    expect_counterexample_on("l_field_assign_sub", "subtraction overflow");
}

#[test]
fn liar_tuple_field_assign_add_is_refuted() {
    expect_counterexample_on("l_tuple_field_assign_add", "addition overflow");
}

#[test]
fn liar_index_assign_add_is_refuted() {
    expect_counterexample_on("l_index_assign_add", "addition overflow");
}

#[test]
fn liar_nested_index_assign_add_is_refuted() {
    expect_counterexample_on("l_nested_index_assign_add", "addition overflow");
}

#[test]
fn liar_underscore_assign_div_is_refuted() {
    expect_counterexample_on("l_underscore_assign_div", "division by zero");
}

#[test]
fn liar_field_assign_index_read_is_refuted() {
    expect_counterexample_on("l_field_assign_index_read", "index_bounds_check");
}

#[test]
fn liar_field_assign_nested_div_is_refuted() {
    expect_counterexample_on("l_field_assign_nested_div", "division by zero");
}

#[test]
fn liar_array_element_field_assign_add_is_refuted() {
    expect_counterexample_on("l_array_element_field_assign_add", "addition overflow");
}

#[test]
fn liar_mut_ref_alias_field_assign_add_is_refuted() {
    expect_counterexample_on("l_mut_ref_alias_field_assign_add", "addition overflow");
}

#[test]
fn control_field_assign_add_verifies() {
    expect_verified("c_field_assign_add");
}

#[test]
fn control_tuple_field_assign_add_verifies() {
    expect_verified("c_tuple_field_assign_add");
}

#[test]
fn control_index_assign_add_verifies() {
    expect_verified("c_index_assign_add");
}

#[test]
fn control_underscore_assign_div_verifies() {
    expect_verified("c_underscore_assign_div");
}

#[test]
fn control_field_assign_index_read_verifies() {
    expect_verified("c_field_assign_index_read");
}

#[test]
fn gated_loop_field_assign_add_fails_closed() {
    expect_error_containing(
        "g_loop_field_assign_add",
        &[LOOP_HAVOC_SITE_REFUSAL, "`i + 1u8`"],
    );
}

// ---- 26: projected compound assignment --------------------------------------

#[test]
fn liar_field_compound_add_is_refuted() {
    expect_counterexample_on("l_field_compound_add", "addition overflow");
}

#[test]
fn liar_tuple_field_compound_sub_is_refuted() {
    expect_counterexample_on("l_tuple_field_compound_sub", "subtraction overflow");
}

#[test]
fn liar_field_compound_shl_is_refuted() {
    expect_counterexample_on("l_field_compound_shl", "shift overflow");
}

#[test]
fn liar_field_compound_bitxor_div_is_refuted() {
    expect_counterexample_on("l_field_compound_bitxor_div", "division by zero");
}

#[test]
fn liar_temporary_tuple_compound_add_is_refuted() {
    expect_counterexample_on("l_temporary_tuple_compound_add", "addition overflow");
}

#[test]
fn control_field_compound_add_verifies() {
    expect_verified("c_field_compound_add");
}

#[test]
fn control_tuple_field_compound_add_verifies() {
    expect_verified("c_tuple_field_compound_add");
}

#[test]
fn control_field_compound_shl_verifies() {
    expect_verified("c_field_compound_shl");
}

#[test]
fn control_field_compound_bitxor_div_verifies() {
    expect_verified("c_field_compound_bitxor_div");
}

#[test]
fn control_field_assign_then_compound_verifies() {
    expect_verified("c_field_assign_then_compound");
}

#[test]
fn control_temporary_tuple_compound_keeps_sources_verifies() {
    expect_verified("c_temporary_tuple_compound_keeps_sources");
}

// ---- 26: projected compound write dropped from the state (havoc) ------------

#[test]
fn liar_field_compound_then_stale_read_fails_closed() {
    expect_error_containing("l_field_compound_then_stale_read", &[UNRESOLVED, "`s`"]);
}

#[test]
fn liar_local_tuple_compound_then_stale_read_fails_closed() {
    expect_error_containing(
        "l_local_tuple_compound_then_stale_read",
        &[UNRESOLVED, "`p`"],
    );
}

#[test]
fn liar_param_tuple_compound_then_stale_read_fails_closed() {
    // Review round 1 (F1): the projected-compound root is POISONED, not
    // havocked, so the stale read is an Error rather than a Counterexample.
    expect_error_containing(
        "l_param_tuple_compound_then_stale_read",
        &[UNRESOLVED, "`p`"],
    );
}

#[test]
fn liar_param_struct_compound_then_stale_read_fails_closed() {
    expect_error_containing(
        "l_param_struct_compound_then_stale_read",
        &[UNRESOLVED, "`s`"],
    );
}

#[test]
fn liar_nested_field_compound_then_stale_read_fails_closed() {
    expect_error_containing(
        "l_nested_field_compound_then_stale_read",
        &[UNRESOLVED, "`w`"],
    );
}

#[test]
fn liar_array_element_field_compound_then_stale_read_fails_closed() {
    expect_error_containing(
        "l_array_element_field_compound_then_stale_read",
        &[UNRESOLVED, "`v`"],
    );
}

#[test]
fn liar_field_compound_twice_overflows_fails_closed() {
    expect_error_containing("l_field_compound_twice_overflows", &[UNRESOLVED, "`s`"]);
}

#[test]
fn gated_field_compound_twice_safe_fails_closed() {
    expect_error_containing("g_field_compound_twice_safe", &[UNRESOLVED, "`s`"]);
}

#[test]
fn gated_field_compound_then_other_field_read_fails_closed() {
    expect_error_containing(
        "g_field_compound_then_other_field_read",
        &[UNRESOLVED, "`s`"],
    );
}

#[test]
fn gated_call_rooted_compound_is_refused() {
    expect_error_containing("g_call_rooted_compound", &[PROJECTED_ROOT_REFUSAL, "get"]);
}

// ---- 27: if-let / while-let scrutinee ---------------------------------------

#[test]
fn liar_if_let_scrutinee_index_arith_is_refuted() {
    expect_counterexample_on("l_if_let_scrutinee_index_arith", "addition overflow");
}

#[test]
fn liar_if_let_scrutinee_add_is_refuted() {
    expect_counterexample_on("l_if_let_scrutinee_add", "addition overflow");
}

#[test]
fn liar_if_let_scrutinee_nested_div_is_refuted() {
    expect_counterexample_on("l_if_let_scrutinee_nested_div", "division by zero");
}

#[test]
fn liar_while_let_scrutinee_add_is_refuted() {
    expect_counterexample_on("l_while_let_scrutinee_add", "addition overflow");
}

#[test]
fn liar_else_if_let_scrutinee_add_is_refuted() {
    expect_counterexample_on("l_else_if_let_scrutinee_add", "addition overflow");
}

#[test]
fn control_if_let_scrutinee_index_arith_verifies() {
    expect_verified("c_if_let_scrutinee_index_arith");
}

#[test]
fn control_while_let_scrutinee_add_verifies() {
    expect_verified("c_while_let_scrutinee_add");
}

#[test]
fn control_else_if_let_scrutinee_add_verifies() {
    expect_verified("c_else_if_let_scrutinee_add");
}

#[test]
fn control_if_let_plain_verifies() {
    expect_verified("c_if_let_plain");
}

#[test]
fn gated_nested_if_let_binding_scrutinee_fails_closed() {
    expect_error_containing("g_nested_if_let_binding_scrutinee", &[UNRESOLVED, "`v`"]);
}

// =============================================================================
// Cluster rank 2 — invalidation leaves the BARE name (2026-09-15)
// =============================================================================

fn verify_c2(func: &str) -> VerifyResult {
    verify(&format!("c2_{func}"), func, SRC_C2)
}

fn expect_c2_verified(func: &str) {
    match verify_c2(func) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

/// Fail-closed error containing every needle (a liar or a gated true claim).
fn expect_c2_error_containing(func: &str, needles: &[&str]) {
    match verify_c2(func) {
        VerifyResult::Error { message } if needles.iter().all(|n| message.contains(n)) => {}
        other => {
            panic!("{func}: expected the fail-closed error containing {needles:?}, got {other:?}")
        }
    }
}

/// The invalidation poison's lowering note (the variable name is reported
/// under its source spelling).
const POISON_NOTE: &str = "vc_extraction does not track is unknown, so this read fails closed";
const LOOP_METHOD_REFUSAL: &str =
    "inside a loop body may change it, and the loop frame does not havoc a method receiver";
/// The refusal of a statement in a block of a run-time assertion's condition
/// (`assertion_operand_statement_soundness`). It comes before the poisoned
/// read that used to refuse the liars that write in an assertion argument.
const ASSERTION_OPERAND_STATEMENT_REFUSAL: &str = "the lane reads only the block's value";

fn expect_c2_poisoned(func: &str, var: &str) {
    let unresolved = format!("unresolved variable `{var}`");
    expect_c2_error_containing(func, &[&unresolved, POISON_NOTE]);
}

const SRC_C2: &str = r#"
use std::ops::AddAssign;

struct Pl {
    f: u8,
}

struct S9 {
    a: u64,
}

impl S9 {
    fn get(&self) -> u64 {
        self.a
    }
}

fn bump_plain(mut q: u64) -> u64 {
    q.add_assign(1u64);
    q
}

fn blk_plain(mut q: u64) -> u64 {
    {
        q = q + 1u64;
    }
    q
}

fn pure_helper(q: u64) -> u64 {
    let _k: u32 = q.count_ones();
    q
}

fn assign_helper(mut q: u64) -> u64 {
    q = q + 1u64;
    q
}

// ---- 33: method call on a declared scalar receiver ---------------------------

// LIAR c33a: asserts x == 0 after x = 5.
#[trust_vc::requires(x == 0u64)]
fn l2_reassigned_param_min_read(mut x: u64) {
    x = 5u64;
    let _y: u64 = x.min(3u64);
    trust_vc::assert!(x == 0u64);
}

// LIAR c33b: returns 5.
#[trust_vc::requires(n == 0u64)]
#[trust_vc::ensures(result == 0u64)]
fn l2_reassigned_param_count_ones_return(mut n: u64) -> u64 {
    n = 5u64;
    let _k: u32 = n.count_ones();
    n
}

// LIAR c33c: n == 1 at the assert.
#[trust_vc::requires(n == 0u64)]
fn l2_incremented_param_max_read(mut n: u64) {
    n = n + 1u64;
    n.max(2u64);
    trust_vc::assert!(n == 0u64);
}

// LIAR c33d: `add_assign` on a never-reassigned `mut` param.
#[trust_vc::requires(x == 0u64)]
fn l2_param_add_assign_read(mut x: u64) {
    x.add_assign(1u64);
    trust_vc::assert!(x == 0u64);
}

// LIAR r8: returns 1.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(result == 0u64)]
fn l2_param_add_assign_return(mut x: u64) -> u64 {
    x.add_assign(1u64);
    x
}

// LIAR c9s: a struct receiver classified pure, but the field write reverted.
#[trust_vc::requires(s.a == 0u64)]
fn l2_struct_field_write_then_getter(mut s: S9) {
    s.a = 5u64;
    let _g: u64 = s.get();
    trust_vc::assert!(s.a == 0u64);
}

// CONTROL: an immutable scalar parameter keeps its entry symbol.
#[trust_vc::requires(x == 0u64)]
fn c2_immutable_param_count_ones_read(x: u64) {
    let _k: u32 = x.count_ones();
    trust_vc::assert!(x == 0u64);
}

// CONTROL: a method result on an immutable param.
#[trust_vc::ensures(true)]
fn c2_immutable_param_min_result(x: u64) {
    let y: u64 = x.min(3u64);
    trust_vc::assert!(y <= 3u64);
}

// CONTROL: several pure methods on an immutable param.
#[trust_vc::requires(x == 3u64)]
fn c2_immutable_param_methods(x: u64) {
    let y: u64 = x.wrapping_add(1u64);
    let z: u64 = x.saturating_sub(1u64);
    trust_vc::assert!(x == 3u64);
    trust_vc::assert!(y == 4u64 && z == 2u64);
}

// CONTROL: pure reads on a collection parameter stay framed.
#[trust_vc::requires(v.len() > 0usize && v[0usize] == 3u64)]
fn c2_collection_param_pure_reads(v: Vec<u64>) {
    let _n: usize = v.len();
    let _f: Option<&u64> = v.get(0usize);
    trust_vc::assert!(v[0usize] == 3u64);
}

// CONTROL: a pure getter on a struct parameter stays framed.
#[trust_vc::requires(s.a == 3u64)]
fn c2_struct_param_pure_getter(s: S9) {
    let _g: u64 = s.get();
    trust_vc::assert!(s.a == 3u64);
}

// CONTROL: a pure getter on a let-local struct inside an invariant loop.
#[trust_vc::ensures(true)]
fn c2_struct_local_getter_in_loop(n: u64) {
    let c = S9 { a: 5u64 };
    let mut i: u64 = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let _g: u64 = c.get();
        i = i + 1u64;
    }
    trust_vc::assert!(c.a == 5u64);
}

// CONTROL: a pure method on an immutable param inside a branch.
#[trust_vc::requires(x == 0u64)]
fn c2_immutable_param_method_in_branch(b: bool, x: u64) {
    if b {
        let _k: u32 = x.count_ones();
    }
    trust_vc::assert!(x == 0u64);
}

// CONTROL: a branch-local receiver does not poison anything outside.
#[trust_vc::ensures(true)]
fn c2_branch_local_receiver(b: bool) {
    let mut y: u64 = 0u64;
    if b {
        let k: u64 = 3u64;
        let _c: u32 = k.count_ones();
        y = 1u64;
    }
    trust_vc::assert!(y <= 1u64);
}

// GATED: runtime-true, HEAD `Verified` through the entry symbol.
#[trust_vc::requires(x == 0u64)]
fn g2_mut_param_count_ones_read(mut x: u64) {
    let _k: u32 = x.count_ones();
    trust_vc::assert!(x == 0u64);
}

// GATED: runtime-true, HEAD `Verified` (the write restores the entry value).
#[trust_vc::requires(x == 0u64)]
fn g2_rewritten_param_count_ones_read(mut x: u64) {
    x = 0u64;
    let _k: u32 = x.count_ones();
    trust_vc::assert!(x == 0u64);
}

// GATED: runtime-true pure method on a `mut` param in a branch.
#[trust_vc::requires(x == 0u64)]
fn g2_mut_param_method_in_branch(b: bool, mut x: u64) {
    if b {
        let _k: u32 = x.count_ones();
    }
    trust_vc::assert!(x == 0u64);
}

// GATED: runtime-true pure method on a `mut` param inside a loop body.
#[trust_vc::requires(x == 0u64)]
fn g2_mut_param_method_in_loop(mut x: u64) {
    let mut i: u64 = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(i <= 3u64 && x == 0u64);
        let _k: u32 = x.count_ones();
        i = i + 1u64;
    }
    trust_vc::assert!(x == 0u64);
}

// ---- 4 / 12: declared name written in a nested block -----------------------

// LIAR c04a.
#[trust_vc::requires(x == 0u64)]
fn l2_block_write_param_read(mut x: u64) {
    {
        x = 2u64;
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR c04b.
#[trust_vc::requires(x == 0u64)]
fn l2_unsafe_write_param_read(mut x: u64) {
    unsafe {
        x = 2u64;
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR c04c.
#[trust_vc::requires(x == 0u64)]
fn l2_value_block_write_param_read(mut x: u64) {
    let _t: u64 = {
        x = 2u64;
        3u64
    };
    trust_vc::assert!(x == 0u64);
}

// LIAR c04d: returns 2 when b.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(result == 0u64)]
fn l2_block_conditional_write_param_return(b: bool, mut x: u64) -> u64 {
    {
        if b {
            x = 2u64;
        }
    }
    x
}

// LIAR c04e: returns 2.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(result == 0u64)]
fn l2_block_write_param_return(mut x: u64) -> u64 {
    {
        x = 2u64;
    }
    x
}

// LIAR c04f.
#[trust_vc::requires(s.f == 0u8)]
fn l2_block_field_write_param_read(mut s: Pl) {
    {
        s.f = 1u8;
    }
    trust_vc::assert!(s.f == 0u8);
}

// LIAR r5: the value block in the right operand writes x.
#[trust_vc::requires(x == 0u64)]
fn l2_operand_value_block_write_then_read(mut x: u64) {
    let v: u64 = x.min(3u64) + {
        x = 9u64;
        0u64
    };
    trust_vc::assert!(x == 0u64);
    trust_vc::assert!(v == 0u64);
}

// LIAR r7: a value block inside an array literal writes x.
#[trust_vc::requires(x == 0u64)]
fn l2_array_literal_value_block_write_then_read(mut x: u64) {
    let _t: u64 = [{
        x = 1u64;
        0u64
    }][0usize];
    trust_vc::assert!(x == 0u64);
}

// LIAR r1: a method call in a block.
#[trust_vc::requires(x == 0u64)]
fn l2_block_method_add_assign(mut x: u64) {
    {
        x.add_assign(1u64);
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR r1b: a method call in `unsafe {}`.
#[trust_vc::requires(x == 0u64)]
fn l2_unsafe_method_add_assign(mut x: u64) {
    unsafe {
        x.add_assign(1u64);
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR r2: a method call in an `if` branch.
#[trust_vc::requires(x == 0u64)]
fn l2_if_method_add_assign(b: bool, mut x: u64) {
    if b {
        x.add_assign(1u64);
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR s5: a method call in a value-position `if` branch.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn l2_if_value_method_add_assign(b: bool, mut x: u64) -> u64 {
    let y: u64 = if b {
        x.add_assign(1u64);
        1u64
    } else {
        2u64
    };
    trust_vc::assert!(x == 0u64);
    y
}

// LIAR r2b: a method call in a `match` arm.
#[trust_vc::requires(x == 0u64)]
fn l2_match_method_add_assign(b: bool, mut x: u64) {
    match b {
        true => {
            x.add_assign(1u64);
        }
        false => {}
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR r3: the loop frame pinned the receiver (invariant falsely preserved).
#[trust_vc::requires(x == 0u64)]
fn l2_while_invariant_method_add_assign(mut x: u64) {
    let mut i: u64 = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(i <= 3u64 && x == 0u64);
        x.add_assign(1u64);
        i = i + 1u64;
    }
}

// LIAR s3: no invariant, post-loop read.
#[trust_vc::requires(x == 0u64)]
fn l2_while_method_add_assign(mut x: u64) {
    let mut i: u64 = 0u64;
    while i < 3u64 {
        x.add_assign(1u64);
        i = i + 1u64;
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR s4.
#[trust_vc::requires(x == 0u64)]
fn l2_for_method_add_assign(mut x: u64) {
    for _i in 0u64..3u64 {
        x.add_assign(1u64);
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR s1: witness o = Some(_).
#[trust_vc::requires(x == 0u64)]
fn l2_while_let_method_add_assign(mut x: u64, o: Option<u64>) {
    let mut c: Option<u64> = o;
    while let Some(_v) = c {
        x.add_assign(1u64);
        c = None;
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR s2: a closure calls the method on its capture.
#[trust_vc::requires(x == 0u64)]
fn l2_closure_method_add_assign(mut x: u64) {
    let mut f = || x.add_assign(1u64);
    f();
    trust_vc::assert!(x == 0u64);
}

// LIAR s6: a closure assigns its captured `mut` parameter.
#[trust_vc::requires(x == 0u64)]
fn l2_closure_assign_param(mut x: u64) {
    let mut f = || {
        x = x + 1u64;
    };
    f();
    trust_vc::assert!(x == 0u64);
}

// CONTROL: a block that only reads.
#[trust_vc::requires(x == 0u64)]
fn c2_block_read_only(x: u64) {
    {
        let y: u64 = x + 1u64;
        trust_vc::assert!(y == 1u64);
    }
    trust_vc::assert!(x == 0u64);
}

// CONTROL: in-block reads, then a straight-line rewrite after the block.
#[trust_vc::requires(x == 0u64)]
fn c2_block_write_then_rewrite(mut x: u64) {
    {
        x = 3u64;
        trust_vc::assert!(x == 3u64);
    }
    x = 4u64;
    trust_vc::assert!(x == 4u64);
}

// CONTROL: a branch-only write at the top level keeps the join havoc model.
#[trust_vc::ensures(true)]
fn c2_if_join_local(b: bool) {
    let mut x: u64 = 0u64;
    if b {
        x = 1u64;
    }
    trust_vc::assert!(x <= 1u64);
}

// GATED: runtime-true, HEAD `Verified` (the block restores the entry value).
#[trust_vc::requires(x == 0u64)]
fn g2_block_write_same_value(mut x: u64) {
    {
        x = 0u64;
    }
    trust_vc::assert!(x == 0u64);
}

// ---- 9: binary operand after a value block ---------------------------------

// LIAR c09a: v == 6.
#[trust_vc::requires(x == 0u64)]
fn l2_value_block_operand_then_param(mut x: u64) {
    let v: u64 = {
        x = 1u64;
        5u64
    } + x;
    trust_vc::assert!(v == 5u64);
}

// LIAR c09b: v == 5 or 6, never 12.
#[trust_vc::requires(x == 7u64)]
fn l2_value_block_operand_then_shadowing_local(b: bool, x: u64) {
    let mut x: u64 = 0u64;
    let v: u64 = {
        if b {
            x = 1u64;
        }
        5u64
    } + x;
    trust_vc::assert!(v == 12u64);
}

// LIAR c09c: the local shadowing the param resolved to the param.
#[trust_vc::requires(x == 7u64)]
fn l2_block_write_shadowing_local_read(x: u64) {
    let mut x: u64 = 0u64;
    {
        x = 1u64;
    }
    trust_vc::assert!(x == 7u64);
}

// ---- 34: invalidated local captured by a later invariant loop --------------

// LIAR c34a: v is 0 or 1.
#[trust_vc::ensures(true)]
fn l2_block_capture_then_invariant_loop(b: bool) {
    let mut x: u64 = 0u64;
    {
        if b {
            x = 1u64;
        }
    }
    let v: u64 = x;
    {
        x = 5u64;
        while x < 8u64 {
            trust_vc::invariant!(x <= 8u64);
            x = x + 1u64;
        }
    }
    trust_vc::assert!(v == 8u64);
}

// ---- 35: callee body axiom built from a reverted parameter -----------------

// LIAR c35d: returns 1.
#[trust_vc::ensures(result == 0u64)]
fn l2_helper_add_assign_axiom() -> u64 {
    bump_plain(0u64)
}

// LIAR c35e: returns 1.
#[trust_vc::ensures(result == 0u64)]
fn l2_helper_block_write_axiom() -> u64 {
    blk_plain(0u64)
}

// CONTROL: a pure helper keeps its body axiom.
#[trust_vc::ensures(result == 0u64)]
fn c2_pure_helper_axiom() -> u64 {
    pure_helper(0u64)
}

// CONTROL: a straight-line assigning helper keeps its body axiom.
#[trust_vc::ensures(result == 1u64)]
fn c2_assign_helper_axiom() -> u64 {
    assign_helper(0u64)
}
"#;

#[test]
fn liar2_reassigned_param_min_read_fails_closed() {
    expect_c2_poisoned("l2_reassigned_param_min_read", "x");
}

#[test]
fn liar2_reassigned_param_count_ones_return_fails_closed() {
    expect_c2_poisoned("l2_reassigned_param_count_ones_return", "n");
}

#[test]
fn liar2_incremented_param_max_read_fails_closed() {
    expect_c2_poisoned("l2_incremented_param_max_read", "n");
}

#[test]
fn liar2_param_add_assign_read_fails_closed() {
    expect_c2_poisoned("l2_param_add_assign_read", "x");
}

#[test]
fn liar2_param_add_assign_return_fails_closed() {
    expect_c2_poisoned("l2_param_add_assign_return", "x");
}

#[test]
fn liar2_struct_field_write_then_getter_fails_closed() {
    expect_c2_poisoned("l2_struct_field_write_then_getter", "s");
}

#[test]
fn control2_immutable_param_count_ones_read_verifies() {
    expect_c2_verified("c2_immutable_param_count_ones_read");
}

#[test]
fn control2_immutable_param_min_result_verifies() {
    expect_c2_verified("c2_immutable_param_min_result");
}

#[test]
fn control2_immutable_param_methods_verifies() {
    expect_c2_verified("c2_immutable_param_methods");
}

#[test]
fn control2_collection_param_pure_reads_verifies() {
    expect_c2_verified("c2_collection_param_pure_reads");
}

#[test]
fn control2_struct_param_pure_getter_verifies() {
    expect_c2_verified("c2_struct_param_pure_getter");
}

#[test]
fn control2_struct_local_getter_in_loop_verifies() {
    expect_c2_verified("c2_struct_local_getter_in_loop");
}

#[test]
fn control2_immutable_param_method_in_branch_verifies() {
    expect_c2_verified("c2_immutable_param_method_in_branch");
}

#[test]
fn control2_branch_local_receiver_verifies() {
    expect_c2_verified("c2_branch_local_receiver");
}

#[test]
fn gated2_mut_param_count_ones_read_fails_closed() {
    expect_c2_poisoned("g2_mut_param_count_ones_read", "x");
}

#[test]
fn gated2_rewritten_param_count_ones_read_fails_closed() {
    expect_c2_poisoned("g2_rewritten_param_count_ones_read", "x");
}

#[test]
fn gated2_mut_param_method_in_branch_fails_closed() {
    expect_c2_poisoned("g2_mut_param_method_in_branch", "x");
}

#[test]
fn gated2_mut_param_method_in_loop_is_refused() {
    expect_c2_error_containing("g2_mut_param_method_in_loop", &[LOOP_METHOD_REFUSAL, "`x`"]);
}

#[test]
fn liar2_block_write_param_read_fails_closed() {
    expect_c2_poisoned("l2_block_write_param_read", "x");
}

#[test]
fn liar2_unsafe_write_param_read_fails_closed() {
    expect_c2_poisoned("l2_unsafe_write_param_read", "x");
}

#[test]
fn liar2_value_block_write_param_read_fails_closed() {
    expect_c2_poisoned("l2_value_block_write_param_read", "x");
}

#[test]
fn liar2_block_conditional_write_param_return_fails_closed() {
    expect_c2_poisoned("l2_block_conditional_write_param_return", "x");
}

#[test]
fn liar2_block_write_param_return_fails_closed() {
    expect_c2_poisoned("l2_block_write_param_return", "x");
}

#[test]
fn liar2_block_field_write_param_read_fails_closed() {
    expect_c2_poisoned("l2_block_field_write_param_read", "s");
}

#[test]
fn liar2_operand_value_block_write_then_read_fails_closed() {
    expect_c2_poisoned("l2_operand_value_block_write_then_read", "x");
}

#[test]
fn liar2_array_literal_value_block_write_then_read_fails_closed() {
    expect_c2_poisoned("l2_array_literal_value_block_write_then_read", "x");
}

#[test]
fn liar2_block_method_add_assign_fails_closed() {
    expect_c2_poisoned("l2_block_method_add_assign", "x");
}

#[test]
fn liar2_unsafe_method_add_assign_fails_closed() {
    expect_c2_poisoned("l2_unsafe_method_add_assign", "x");
}

#[test]
fn liar2_if_method_add_assign_fails_closed() {
    expect_c2_poisoned("l2_if_method_add_assign", "x");
}

#[test]
fn liar2_if_value_method_add_assign_fails_closed() {
    expect_c2_poisoned("l2_if_value_method_add_assign", "x");
}

#[test]
fn liar2_match_method_add_assign_fails_closed() {
    expect_c2_poisoned("l2_match_method_add_assign", "x");
}

#[test]
fn liar2_while_invariant_method_add_assign_is_refused() {
    expect_c2_error_containing(
        "l2_while_invariant_method_add_assign",
        &[LOOP_METHOD_REFUSAL, "`x`"],
    );
}

#[test]
fn liar2_while_method_add_assign_is_refused() {
    expect_c2_error_containing("l2_while_method_add_assign", &[LOOP_METHOD_REFUSAL, "`x`"]);
}

#[test]
fn liar2_for_method_add_assign_is_refused() {
    expect_c2_error_containing("l2_for_method_add_assign", &[LOOP_METHOD_REFUSAL, "`x`"]);
}

#[test]
fn liar2_while_let_method_add_assign_is_refused() {
    expect_c2_error_containing(
        "l2_while_let_method_add_assign",
        &[LOOP_METHOD_REFUSAL, "`x`"],
    );
}

#[test]
fn liar2_closure_method_add_assign_fails_closed() {
    expect_c2_poisoned("l2_closure_method_add_assign", "x");
}

#[test]
fn liar2_closure_assign_param_is_refuted() {
    // The called closure leaves the captured `mut` parameter at a fresh
    // unconstrained `u64`, so the stale claim `x == 0` is refuted at the
    // assertion. Every value any number of runs can leave is covered, so no
    // claim about `x` after the closure verifies unless it holds for all `u64`.
    match verify_c2("l2_closure_assign_param") {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.starts_with("assertion_") => {}
        other => panic!(
            "l2_closure_assign_param: expected a Counterexample on the assertion, got {other:?}"
        ),
    }
}

#[test]
fn control2_block_read_only_verifies() {
    expect_c2_verified("c2_block_read_only");
}

#[test]
fn control2_block_write_then_rewrite_verifies() {
    expect_c2_verified("c2_block_write_then_rewrite");
}

#[test]
fn control2_if_join_local_verifies() {
    expect_c2_verified("c2_if_join_local");
}

#[test]
fn gated2_block_write_same_value_fails_closed() {
    expect_c2_poisoned("g2_block_write_same_value", "x");
}

#[test]
fn liar2_value_block_operand_then_param_fails_closed() {
    expect_c2_poisoned("l2_value_block_operand_then_param", "x");
}

#[test]
fn liar2_value_block_operand_then_shadowing_local_fails_closed() {
    expect_c2_poisoned("l2_value_block_operand_then_shadowing_local", "x");
}

#[test]
fn liar2_block_write_shadowing_local_read_fails_closed() {
    expect_c2_poisoned("l2_block_write_shadowing_local_read", "x");
}

#[test]
fn liar2_block_capture_then_invariant_loop_fails_closed() {
    expect_c2_poisoned("l2_block_capture_then_invariant_loop", "x");
}

#[test]
fn liar2_helper_add_assign_axiom_is_dropped() {
    expect_c2_error_containing(
        "l2_helper_add_assign_axiom",
        &["unknown return type for function 'bump_plain'"],
    );
}

#[test]
fn liar2_helper_block_write_axiom_is_dropped() {
    expect_c2_error_containing(
        "l2_helper_block_write_axiom",
        &["unknown return type for function 'blk_plain'"],
    );
}

#[test]
fn control2_pure_helper_axiom_verifies() {
    expect_c2_verified("c2_pure_helper_axiom");
}

#[test]
fn control2_assign_helper_axiom_verifies() {
    expect_c2_verified("c2_assign_helper_axiom");
}

// ============================================================================
// Cluster rank 3 — value-lane block evaluation drops statement effects
// ============================================================================

fn verify_c3(func: &str) -> VerifyResult {
    verify(&format!("c3_{func}"), func, SRC_C3)
}

fn expect_c3_verified(func: &str) {
    match verify_c3(func) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

/// A liar whose model is refuted once the dropped effect is framed.
fn expect_c3_counterexample(func: &str) {
    match verify_c3(func) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

/// Fail-closed error containing every needle (a liar or a gated true claim).
fn expect_c3_error_containing(func: &str, needles: &[&str]) {
    match verify_c3(func) {
        VerifyResult::Error { message } if needles.iter().all(|n| message.contains(n)) => {}
        other => {
            panic!("{func}: expected the fail-closed error containing {needles:?}, got {other:?}")
        }
    }
}

fn expect_c3_poisoned(func: &str, var: &str) {
    let unresolved = format!("unresolved variable `{var}`");
    expect_c3_error_containing(func, &[&unresolved, POISON_NOTE]);
}

const NESTED_SPEC_ASSERTION_REFUSAL: &str =
    "a spec assertion nested inside an assertion argument is never emitted as an obligation";

const SRC_C3: &str = r#"
use std::ops::AddAssign;

struct Q {
    a: u64,
    b: u64,
}

impl Q {
    fn bump_ret(&mut self) -> u64 {
        let v = {
            self.a.add_assign(1u64);
            0u64
        };
        self.a + v
    }
    fn bump_assert(&mut self) -> u64 {
        assert!({
            self.a.add_assign(1u64);
            true
        });
        self.a
    }
    fn bump_plain(&mut self) -> u64 {
        self.a.add_assign(1u64);
        self.a
    }
}

fn helper_mut_binding(mut q: Q) -> u64 {
    assert!({
        q.a.add_assign(1u64);
        true
    });
    q.a
}

fn write_one(a: &mut u64) -> u64 {
    *a = 1u64;
    0u64
}

fn helper_block_join(mut a: u64, b: bool) -> u64 {
    let v = {
        if b {
            a = 1u64;
        }
        a
    };
    v
}

fn helper_pure_block(a: u64) -> u64 {
    let v = {
        let t = a + 1u64;
        t
    };
    v
}

// ---- A: statement effects inside a value-lane block ------------------------

// LIAR v6: returns 1 at k = 0, b = true.
#[trust_vc::ensures(result == 0u64)]
fn l3_match_arm_join_return(k: u64, b: bool) -> u64 {
    let mut x = 0u64;
    match k {
        0u64 => {
            if b {
                x = 1u64;
            }
            x
        }
        _ => 0u64,
    }
}

// LIAR v7: panics at c = b = true.
#[trust_vc::ensures(true)]
fn l3_let_if_branch_join(c: bool, b: bool) {
    let mut x = 0u64;
    let y = if c {
        if b {
            x = 1u64;
        }
        x
    } else {
        0u64
    };
    trust_vc::assert!(y == 0u64);
}

// LIAR v5: panics at k = 0, b = true.
#[trust_vc::ensures(true)]
fn l3_let_match_arm_join(k: u64, b: bool) {
    let mut x = 0u64;
    let y = match k {
        0u64 => {
            if b {
                x = 1u64;
            }
            x
        }
        _ => 0u64,
    };
    trust_vc::assert!(y == 0u64);
}

// LIAR c20a: returns 1 at b = true.
#[trust_vc::ensures(result == 0u64)]
fn l3_return_block_if_else_join(b: bool) -> u64 {
    let mut x = 0u64;
    {
        if b {
            x = 1u64;
        } else {
            x = 2u64;
        }
        x
    }
}

// LIAR c01a: panics at b = true.
#[trust_vc::ensures(true)]
fn l3_let_init_if_write(b: bool) {
    let mut x = 0u64;
    let v: u64 = {
        let _w: u64 = if b {
            x = 1u64;
            3u64
        } else {
            3u64
        };
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR j1: panics.
#[trust_vc::ensures(true)]
fn l3_let_init_paren_assign() {
    let mut x: u64 = 0u64;
    let v: u64 = {
        let _w = (x = 1u64);
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR j2: panics at n = 0.
#[trust_vc::ensures(true)]
fn l3_let_init_match_arm_assign(n: u64) {
    let mut x: u64 = 0u64;
    let v: u64 = {
        let _w = match n {
            0u64 => x = 1u64,
            _ => (),
        };
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR j3: panics.
#[trust_vc::ensures(true)]
fn l3_let_init_compound_assign() {
    let mut x: u64 = 0u64;
    let v: u64 = {
        let _w = x += 1u64;
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR j5: returns 1.
#[trust_vc::ensures(result == 0u64)]
fn l3_return_block_let_init_assign() -> u64 {
    let mut x = 0u64;
    {
        let _w = (x = 1u64);
        x
    }
}

// LIAR j6: panics.
#[trust_vc::ensures(true)]
fn l3_assign_rhs_assign() {
    let mut x: u64 = 0u64;
    let mut u: () = ();
    let v: u64 = {
        u = (x = 1u64);
        x
    };
    let _ = u;
    trust_vc::assert!(v == 0u64);
}

// LIAR j7: panics.
#[trust_vc::ensures(true)]
fn l3_let_init_tuple_assign() {
    let mut x: u64 = 0u64;
    let v: u64 = {
        let _w = (x = 1u64, 0u64);
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR s2: panics (x == 3).
#[trust_vc::ensures(true)]
fn l3_non_tail_while() {
    let mut x = 0u64;
    let v: u64 = {
        while x < 3u64 {
            x = x + 1u64;
        }
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR s3: panics.
#[trust_vc::ensures(true)]
fn l3_non_tail_loop() {
    let mut x = 0u64;
    let v: u64 = {
        loop {
            x = 1u64;
            break;
        }
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR s4: panics.
#[trust_vc::ensures(true)]
fn l3_closure_call_in_block() {
    let mut x = 0u64;
    let v: u64 = {
        let mut g = || {
            x = 1u64;
        };
        g();
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR s6: panics at o = Some(_).
#[trust_vc::ensures(true)]
fn l3_non_tail_if_let(o: Option<u64>) {
    let mut x = 0u64;
    let v: u64 = {
        if let Some(_) = o {
            x = 1u64;
        }
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR s16: panics.
#[trust_vc::ensures(true)]
fn l3_vec_macro_arg_write() {
    let mut x = 0u64;
    let v: u64 = {
        let _w = vec![{
            x = 1u64;
            1u64
        }];
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR s19: panics.
#[trust_vc::ensures(true)]
fn l3_nested_block_stmt() {
    let mut x = 0u64;
    let v: u64 = {
        {
            x = 1u64;
        }
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR s25: panics.
#[trust_vc::ensures(true)]
fn l3_assign_rhs_block_writes_other() {
    let mut x = 0u64;
    let mut y = 0u64;
    let v: u64 = {
        x = {
            y = 5u64;
            1u64
        };
        y
    };
    let _ = x;
    trust_vc::assert!(v == 0u64);
}

// LIAR s1: panics.
#[trust_vc::ensures(true)]
fn l3_let_init_mut_borrow_call() {
    let mut x = 0u64;
    let v: u64 = {
        let _k = write_one(&mut x);
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR m1: panics at x = 0.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn l3_method_stmt_mut_param(mut x: u64) {
    let v: u64 = {
        x.add_assign(1u64);
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR m4: panics at x = 0.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn l3_let_init_method_mut_param(mut x: u64) {
    let v: u64 = {
        let _u = x.add_assign(1u64);
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR m5: panics.
#[trust_vc::ensures(true)]
fn l3_let_init_method_local() {
    let mut x = 0u64;
    let v: u64 = {
        let _u = x.add_assign(1u64);
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR o1e: panics.
#[trust_vc::ensures(true)]
fn l3_value_block_field_receiver() {
    let mut s = Q { a: 0u64, b: 0u64 };
    let v: u64 = {
        s.a.add_assign(1u64);
        s.a
    };
    trust_vc::assert!(v == 0u64);
}

// CONTROL j8: a modeled statement-lane write.
#[trust_vc::ensures(true)]
fn c3_let_paren_assign_statement_lane() {
    let mut x: u64 = 0u64;
    let _w = (x = 1u64);
    trust_vc::assert!(x == 1u64);
}

// CONTROL nt1: a non-tail write nothing reads later in the block.
#[trust_vc::ensures(true)]
fn c3_non_tail_write_unread(b: bool) {
    let mut x = 0u64;
    let v: u64 = {
        if b {
            x = 1u64;
        }
        5u64
    };
    trust_vc::assert!(v == 5u64);
}

// CONTROL nt2: a non-tail `if` with only a spec assertion.
#[trust_vc::ensures(true)]
fn c3_non_tail_assert_only(b: bool) {
    let x = 0u64;
    let v: u64 = {
        if b {
            trust_vc::assert!(x == 0u64);
        }
        5u64
    };
    trust_vc::assert!(v == 5u64);
}

// CONTROL le1: a pure method in a value-block `let`.
#[trust_vc::ensures(true)]
fn c3_value_block_pure_len(v: Vec<u64>) {
    let n: usize = {
        let k = v.len();
        k
    };
    trust_vc::assert!(n == v.len());
}

// CONTROL c6: a modeled assignment statement inside a value block.
#[trust_vc::ensures(true)]
fn c3_value_block_modeled_assign() {
    let mut x = 0u64;
    let v: u64 = {
        x = 1u64;
        x
    };
    trust_vc::assert!(v == 1u64);
}

// CONTROL s24: the assignment overwrites what its RHS wrote.
#[trust_vc::ensures(true)]
fn c3_assign_rhs_overwritten(b: bool) {
    let mut x = 0u64;
    let v: u64 = {
        x = if b {
            x = 5u64;
            1u64
        } else {
            1u64
        };
        x
    };
    trust_vc::assert!(v == 1u64);
}

// CONTROL c14: pure reads in both branches of a value `if`.
#[trust_vc::ensures(true)]
fn c3_value_if_pure_len(v: Vec<u64>, b: bool) {
    let n: usize = if b {
        let k = v.len();
        k
    } else {
        v.len()
    };
    trust_vc::assert!(n == v.len());
}

// CONTROL c18: a spec assertion statement inside a value block.
#[trust_vc::ensures(true)]
fn c3_value_block_assert_statement() {
    let x = 0u64;
    let v: u64 = {
        assert!(x == 0u64);
        x
    };
    trust_vc::assert!(v == 0u64);
}

// CONTROL c9: a pure value-block helper keeps its body axiom.
#[trust_vc::requires(a < 10u64)]
#[trust_vc::ensures(true)]
fn c3_pure_block_helper_axiom(a: u64) {
    let r = helper_pure_block(a);
    trust_vc::assert!(r == a + 1u64);
}

// GATED c13: runtime-true, HEAD `Verified` through the pre-write value.
#[trust_vc::ensures(true)]
fn g3_value_block_join_read_bound(b: bool) {
    let mut x = 0u64;
    let v: u64 = {
        if b {
            x = 1u64;
        }
        x
    };
    trust_vc::assert!(v <= 1u64);
}

// ---- B: an effectful `if` condition / `match` scrutinee / index base -------

// LIAR g1: panics.
#[trust_vc::ensures(true)]
fn l3_if_cond_block_assign(b: bool) {
    let mut x: u64 = 0u64;
    let v: u64 = if ({
        x = 1u64;
        b || !b
    }) {
        x
    } else {
        7u64
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR g2: panics.
#[trust_vc::ensures(true)]
fn l3_match_scrutinee_block_assign() {
    let mut x: u64 = 0u64;
    let v: u64 = match ({
        x = 1u64;
        0u64
    }) {
        0u64 => x,
        _ => 9u64,
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR g3: returns 1.
#[trust_vc::ensures(result == 0u64)]
fn l3_return_if_cond_block_assign(b: bool) -> u64 {
    let mut x: u64 = 0u64;
    if ({
        x = 1u64;
        b || !b
    }) {
        x
    } else {
        7u64
    }
}

// LIAR g4: returns 1.
#[trust_vc::ensures(result == 0u64)]
fn l3_return_match_scrutinee_block_assign() -> u64 {
    let mut x: u64 = 0u64;
    match ({
        x = 1u64;
        0u64
    }) {
        0u64 => x,
        _ => 9u64,
    }
}

// LIAR g5: panics at b = true.
#[trust_vc::ensures(true)]
fn l3_if_cond_block_join_else_read(b: bool) {
    let mut x: u64 = 0u64;
    let v: u64 = if ({
        if b {
            x = 1u64;
        }
        false
    }) {
        7u64
    } else {
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR g6: panics at b = true (reads arr[1]).
#[trust_vc::ensures(true)]
fn l3_index_base_block_join(b: bool) {
    let mut x: u64 = 0u64;
    let arr: [u64; 2] = [10u64, 20u64];
    let v: u64 = ({
        if b {
            x = 1u64;
        }
        arr
    })[x as usize];
    trust_vc::assert!(v == 10u64);
}

// LIAR g6u: panics.
#[trust_vc::ensures(true)]
fn l3_index_base_block_assign() {
    let mut x: u64 = 0u64;
    let arr: [u64; 2] = [10u64, 20u64];
    let v: u64 = ({
        x = 1u64;
        arr
    })[x as usize];
    trust_vc::assert!(v == 10u64);
}

// LIAR b14: panics at b = true, x = 0.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn l3_match_scrutinee_join_param(b: bool, mut x: u64) {
    let v: u64 = match ({
        if b {
            x = 1u64;
        }
        0u64
    }) {
        0u64 => x,
        _ => 9u64,
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR i14: panics.
#[trust_vc::ensures(true)]
fn l3_assert_arg_if_cond_block() {
    let mut x: u64 = 0u64;
    trust_vc::assert!(if ({
        x = 1u64;
        true
    }) {
        x == 0u64
    } else {
        false
    });
}

// LIAR m3: panics at x = 0.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn l3_if_cond_method_mut_param(mut x: u64) {
    let v: u64 = if ({
        x.add_assign(1u64);
        true
    }) {
        x
    } else {
        0u64
    };
    trust_vc::assert!(v == 0u64);
}

// CONTROL c4: a pure condition block.
#[trust_vc::ensures(true)]
fn c3_if_cond_pure_block() {
    let v: u64 = if ({
        let t = 3u64;
        t > 2u64
    }) {
        1u64
    } else {
        2u64
    };
    trust_vc::assert!(v == 1u64);
}

// CONTROL c5: an effectful condition whose branches do not read the write.
#[trust_vc::ensures(true)]
fn c3_if_cond_write_unread(b: bool) {
    let mut x = 0u64;
    let v: u64 = if ({
        x = 1u64;
        b
    }) {
        5u64
    } else {
        7u64
    };
    trust_vc::assert!(v >= 5u64);
}

// CONTROL c7: an effectful scrutinee whose arms do not read the write.
#[trust_vc::ensures(true)]
fn c3_match_scrutinee_write_unread(k: u64) {
    let mut x = 0u64;
    let v: u64 = match ({
        x = 1u64;
        k
    }) {
        0u64 => 1u64,
        _ => 2u64,
    };
    trust_vc::assert!(v >= 1u64);
}

// ---- C: effects inside a spec macro statement's arguments ------------------

// LIAR a9: panics.
#[trust_vc::ensures(true)]
fn l3_assert_arg_write_value_block() {
    let mut x: u64 = 0u64;
    let v: u64 = {
        assert!({
            x = 1u64;
            true
        });
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR k1: panics.
#[trust_vc::ensures(true)]
fn l3_assert_eq_arg_write_value_block() {
    let mut x: u64 = 0u64;
    let v: u64 = {
        assert_eq!(
            {
                x = 1u64;
                0u64
            },
            0u64
        );
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR k2: returns 1.
#[trust_vc::ensures(result == 0u64)]
fn l3_return_block_assert_arg_write() -> u64 {
    let mut x = 0u64;
    {
        assert!({
            x = 1u64;
            true
        });
        x
    }
}

// LIAR a9v: panics at b = true.
#[trust_vc::ensures(true)]
fn l3_branch_assert_arg_write(b: bool) {
    let mut x = 0u64;
    let v: u64 = if b {
        assert!({
            x = 1u64;
            true
        });
        x
    } else {
        0u64
    };
    trust_vc::assert!(v == 0u64);
}

// CONTROL c8: a pure block in an assertion argument.
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn c3_assert_arg_pure_block(x: u64) {
    trust_vc::assert!({
        let t = x + 1u64;
        t > x
    });
}

// CONTROL: a block in an assertion argument whose `let` binds a plain value.
#[trust_vc::requires(x < 100u64)]
#[trust_vc::ensures(true)]
fn c3_assert_arg_plain_let_block(x: u64) {
    trust_vc::assert!({
        let t = x;
        t < 100u64
    });
}

// ---- D: a spec assertion nested in an assertion argument -------------------

// LIAR k5: panics.
#[trust_vc::ensures(true)]
fn l3_nested_spec_assert_false() {
    trust_vc::assert!({
        trust_vc::assert!(false);
        true
    });
}

// LIAR: the plain-`assert!` spelling of k5; panics.
#[trust_vc::ensures(true)]
fn l3_nested_plain_assert_false() {
    assert!({
        assert!(false);
        true
    });
}

// LIAR a6: panics at b = true.
#[trust_vc::ensures(true)]
fn l3_nested_spec_assert_after_write(b: bool) {
    let mut x: u64 = 0u64;
    trust_vc::assert!({
        if b {
            x = 1u64;
        }
        trust_vc::assert!(x == 0u64);
        true
    });
}

// ---- E: a local macro whose transcriber ends in a semicolon-less effect ----

// LIAR a1: panics at b = true.
#[trust_vc::ensures(true)]
fn l3_local_macro_tail_if(b: bool) {
    let mut x: u64 = 0u64;
    macro_rules! m {
        () => {
            if b {
                x = 1u64;
            }
        };
    }
    let v: u64 = {
        m!();
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR a2: panics.
#[trust_vc::ensures(true)]
fn l3_local_macro_tail_while() {
    let mut x: u64 = 0u64;
    macro_rules! m {
        () => {
            while x < 3u64 {
                x = x + 1u64;
            }
        };
    }
    let v: u64 = {
        m!();
        x
    };
    trust_vc::assert!(v == 0u64);
}

// LIAR a4: returns 1 at b = true.
#[trust_vc::ensures(result == 0u64)]
fn l3_return_local_macro_tail_if(b: bool) -> u64 {
    let mut x = 0u64;
    macro_rules! m {
        () => {
            if b {
                x = 1u64;
            }
        };
    }
    {
        m!();
        x
    }
}

// LIAR s7: panics at k = 0, x = 0.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn l3_local_macro_tail_match_param(k: u64, mut x: u64) {
    macro_rules! m {
        () => {
            match k {
                0u64 => {
                    x = 1u64;
                }
                _ => {}
            }
        };
    }
    let v: u64 = {
        m!();
        x
    };
    trust_vc::assert!(v == 0u64);
}

// ---- F: autoref through a projected receiver / assertion-argument effects --

// LIAR r4f-o1: `bump_ret` returns 2.
#[trust_vc::requires(pa == 1u64)]
#[trust_vc::ensures(true)]
fn l3_mut_self_autoref_value_block(pa: u64) {
    let mut p = Q { a: pa, b: 0u64 };
    let r = p.bump_ret();
    trust_vc::assert!(r == 1u64);
}

// LIAR r4f-o2: `bump_assert` returns 2.
#[trust_vc::requires(pa == 1u64)]
#[trust_vc::ensures(true)]
fn l3_mut_self_autoref_assert_arg(pa: u64) {
    let mut p = Q { a: pa, b: 0u64 };
    let r = p.bump_assert();
    trust_vc::assert!(r == 1u64);
}

// LIAR r4f-o3: `helper_mut_binding` returns 2.
#[trust_vc::requires(pa == 1u64)]
#[trust_vc::ensures(true)]
fn l3_mut_binding_autoref_assert_arg(pa: u64) {
    let p = Q { a: pa, b: 0u64 };
    let r = helper_mut_binding(p);
    trust_vc::assert!(r == 1u64);
}

// LIAR: `bump_plain` returns 2 (no value block at all).
#[trust_vc::requires(pa == 1u64)]
#[trust_vc::ensures(true)]
fn l3_mut_self_autoref_plain(pa: u64) {
    let mut p = Q { a: pa, b: 0u64 };
    let r = p.bump_plain();
    trust_vc::assert!(r == 1u64);
}

// LIAR: a let-local struct's field autoref; panics.
#[trust_vc::ensures(true)]
fn l3_local_struct_field_autoref() {
    let mut s = Q { a: 0u64, b: 0u64 };
    s.a.add_assign(1u64);
    trust_vc::assert!(s.a == 0u64);
}

// LIAR: the same inside a `let` value block; panics.
#[trust_vc::ensures(true)]
fn l3_local_struct_field_autoref_value_block() {
    let mut s = Q { a: 0u64, b: 0u64 };
    let v: u64 = {
        s.a.add_assign(1u64);
        0u64
    };
    trust_vc::assert!(s.a + v == 0u64);
}

// LIAR: a tuple field autoref; panics.
#[trust_vc::ensures(true)]
fn l3_tuple_field_autoref() {
    let mut p = (0u64, 0u64);
    p.0.add_assign(1u64);
    trust_vc::assert!(p.0 == 0u64);
}

// LIAR: a field autoref inside an `if`; panics at c = true.
#[trust_vc::ensures(true)]
fn l3_if_region_field_autoref(c: bool) {
    let mut s = Q { a: 0u64, b: 0u64 };
    if c {
        s.a.add_assign(1u64);
    }
    trust_vc::assert!(s.a == 0u64);
}

// LIAR: a write in an assertion argument inside an `if`; panics at c = true.
#[trust_vc::ensures(true)]
fn l3_if_region_assert_arg_write(c: bool) {
    let mut x = 0u64;
    if c {
        assert!({
            x = 1u64;
            true
        });
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR: a write in an assertion argument inside a loop body; panics.
#[trust_vc::ensures(true)]
fn l3_loop_assert_arg_write() {
    let mut x = 0u64;
    let mut i = 0u64;
    while i < 3u64 {
        trust_vc::invariant!(i <= 3u64);
        assert!({
            x = 1u64;
            true
        });
        i = i + 1u64;
    }
    trust_vc::assert!(x == 0u64);
}

// LIAR: a contract-less helper whose value block joins a write; panics.
#[trust_vc::ensures(true)]
fn l3_helper_value_block_join_axiom() {
    let r = helper_block_join(0u64, true);
    trust_vc::assert!(r == 0u64);
}

// CONTROL c12: a pure projected method (`clone`).
#[trust_vc::ensures(true)]
fn c3_projected_clone() {
    let s = Q { a: 5u64, b: 0u64 };
    let _c: u64 = s.a.clone();
    trust_vc::assert!(s.b == 0u64);
}

// GATED c10: runtime-true; `count_ones` is not on the pure-name list.
#[trust_vc::ensures(true)]
fn g3_projected_count_ones_local_struct() {
    let s = Q { a: 5u64, b: 0u64 };
    let _n: u32 = s.a.count_ones();
    trust_vc::assert!(s.b == 0u64);
}

// GATED c11: the tuple twin of c10.
#[trust_vc::ensures(true)]
fn g3_projected_count_ones_tuple() {
    let p = (5u64, 0u64);
    let _n: u32 = p.0.count_ones();
    trust_vc::assert!(p.1 == 0u64);
}
"#;

#[test]
fn liar3_match_arm_join_return_fails_closed() {
    expect_c3_poisoned("l3_match_arm_join_return", "x");
}

#[test]
fn liar3_let_if_branch_join_fails_closed() {
    expect_c3_poisoned("l3_let_if_branch_join", "x");
}

#[test]
fn liar3_let_match_arm_join_fails_closed() {
    expect_c3_poisoned("l3_let_match_arm_join", "x");
}

#[test]
fn liar3_return_block_if_else_join_fails_closed() {
    expect_c3_poisoned("l3_return_block_if_else_join", "x");
}

#[test]
fn liar3_let_init_if_write_fails_closed() {
    expect_c3_poisoned("l3_let_init_if_write", "x");
}

#[test]
fn liar3_let_init_paren_assign_fails_closed() {
    expect_c3_poisoned("l3_let_init_paren_assign", "x");
}

#[test]
fn liar3_let_init_match_arm_assign_fails_closed() {
    expect_c3_poisoned("l3_let_init_match_arm_assign", "x");
}

#[test]
fn liar3_let_init_compound_assign_fails_closed() {
    expect_c3_poisoned("l3_let_init_compound_assign", "x");
}

#[test]
fn liar3_return_block_let_init_assign_fails_closed() {
    expect_c3_poisoned("l3_return_block_let_init_assign", "x");
}

#[test]
fn liar3_assign_rhs_assign_fails_closed() {
    expect_c3_poisoned("l3_assign_rhs_assign", "x");
}

#[test]
fn liar3_let_init_tuple_assign_fails_closed() {
    expect_c3_poisoned("l3_let_init_tuple_assign", "x");
}

#[test]
fn liar3_non_tail_while_fails_closed() {
    expect_c3_poisoned("l3_non_tail_while", "x");
}

#[test]
fn liar3_non_tail_loop_fails_closed() {
    expect_c3_poisoned("l3_non_tail_loop", "x");
}

#[test]
fn liar3_closure_call_in_block_fails_closed() {
    expect_c3_poisoned("l3_closure_call_in_block", "x");
}

#[test]
fn liar3_non_tail_if_let_fails_closed() {
    expect_c3_poisoned("l3_non_tail_if_let", "x");
}

#[test]
fn liar3_vec_macro_arg_write_fails_closed() {
    expect_c3_poisoned("l3_vec_macro_arg_write", "x");
}

#[test]
fn liar3_nested_block_stmt_fails_closed() {
    expect_c3_poisoned("l3_nested_block_stmt", "x");
}

#[test]
fn liar3_assign_rhs_block_writes_other_fails_closed() {
    expect_c3_poisoned("l3_assign_rhs_block_writes_other", "y");
}

#[test]
fn liar3_let_init_mut_borrow_call_fails_closed() {
    expect_c3_poisoned("l3_let_init_mut_borrow_call", "x");
}

#[test]
fn liar3_method_stmt_mut_param_fails_closed() {
    expect_c3_poisoned("l3_method_stmt_mut_param", "x");
}

#[test]
fn liar3_let_init_method_mut_param_fails_closed() {
    expect_c3_poisoned("l3_let_init_method_mut_param", "x");
}

#[test]
fn liar3_let_init_method_local_fails_closed() {
    expect_c3_poisoned("l3_let_init_method_local", "x");
}

#[test]
fn liar3_value_block_field_receiver_fails_closed() {
    expect_c3_poisoned("l3_value_block_field_receiver", "s");
}

#[test]
fn control3_let_paren_assign_statement_lane_verifies() {
    expect_c3_verified("c3_let_paren_assign_statement_lane");
}

#[test]
fn control3_non_tail_write_unread_verifies() {
    expect_c3_verified("c3_non_tail_write_unread");
}

#[test]
fn control3_non_tail_assert_only_verifies() {
    expect_c3_verified("c3_non_tail_assert_only");
}

#[test]
fn control3_value_block_pure_len_verifies() {
    expect_c3_verified("c3_value_block_pure_len");
}

#[test]
fn control3_value_block_modeled_assign_verifies() {
    expect_c3_verified("c3_value_block_modeled_assign");
}

#[test]
fn control3_assign_rhs_overwritten_verifies() {
    expect_c3_verified("c3_assign_rhs_overwritten");
}

#[test]
fn control3_value_if_pure_len_verifies() {
    expect_c3_verified("c3_value_if_pure_len");
}

#[test]
fn control3_value_block_assert_statement_verifies() {
    expect_c3_verified("c3_value_block_assert_statement");
}

#[test]
fn control3_pure_block_helper_axiom_verifies() {
    expect_c3_verified("c3_pure_block_helper_axiom");
}

#[test]
fn gated3_value_block_join_read_bound_fails_closed() {
    expect_c3_poisoned("g3_value_block_join_read_bound", "x");
}

#[test]
fn liar3_if_cond_block_assign_fails_closed() {
    expect_c3_poisoned("l3_if_cond_block_assign", "x");
}

#[test]
fn liar3_match_scrutinee_block_assign_fails_closed() {
    expect_c3_poisoned("l3_match_scrutinee_block_assign", "x");
}

#[test]
fn liar3_return_if_cond_block_assign_fails_closed() {
    expect_c3_poisoned("l3_return_if_cond_block_assign", "x");
}

#[test]
fn liar3_return_match_scrutinee_block_assign_fails_closed() {
    expect_c3_poisoned("l3_return_match_scrutinee_block_assign", "x");
}

#[test]
fn liar3_if_cond_block_join_else_read_fails_closed() {
    expect_c3_poisoned("l3_if_cond_block_join_else_read", "x");
}

#[test]
fn liar3_index_base_block_join_fails_closed() {
    expect_c3_poisoned("l3_index_base_block_join", "x");
}

#[test]
fn liar3_index_base_block_assign_fails_closed() {
    expect_c3_poisoned("l3_index_base_block_assign", "x");
}

#[test]
fn liar3_match_scrutinee_join_param_fails_closed() {
    expect_c3_poisoned("l3_match_scrutinee_join_param", "x");
}

#[test]
fn liar3_assert_arg_if_cond_block_fails_closed() {
    expect_c3_error_containing(
        "l3_assert_arg_if_cond_block",
        &[ASSERTION_OPERAND_STATEMENT_REFUSAL],
    );
}

#[test]
fn liar3_if_cond_method_mut_param_fails_closed() {
    expect_c3_poisoned("l3_if_cond_method_mut_param", "x");
}

#[test]
fn control3_if_cond_pure_block_verifies() {
    expect_c3_verified("c3_if_cond_pure_block");
}

#[test]
fn control3_if_cond_write_unread_verifies() {
    expect_c3_verified("c3_if_cond_write_unread");
}

#[test]
fn control3_match_scrutinee_write_unread_verifies() {
    expect_c3_verified("c3_match_scrutinee_write_unread");
}

#[test]
fn liar3_assert_arg_write_value_block_fails_closed() {
    expect_c3_error_containing(
        "l3_assert_arg_write_value_block",
        &[ASSERTION_OPERAND_STATEMENT_REFUSAL],
    );
}

#[test]
fn liar3_assert_eq_arg_write_value_block_fails_closed() {
    expect_c3_error_containing(
        "l3_assert_eq_arg_write_value_block",
        &[ASSERTION_OPERAND_STATEMENT_REFUSAL],
    );
}

#[test]
fn liar3_return_block_assert_arg_write_fails_closed() {
    expect_c3_error_containing(
        "l3_return_block_assert_arg_write",
        &[ASSERTION_OPERAND_STATEMENT_REFUSAL],
    );
}

#[test]
fn liar3_branch_assert_arg_write_fails_closed() {
    expect_c3_error_containing(
        "l3_branch_assert_arg_write",
        &[ASSERTION_OPERAND_STATEMENT_REFUSAL],
    );
}

/// True, but `let t = x + 1u64;` can overflow and the assertion's rendering
/// drops it, so the statement is refused.
#[test]
fn control3_assert_arg_arith_let_block_is_refused() {
    expect_c3_error_containing(
        "c3_assert_arg_pure_block",
        &[ASSERTION_OPERAND_STATEMENT_REFUSAL],
    );
}

#[test]
fn control3_assert_arg_plain_let_block_verifies() {
    expect_c3_verified("c3_assert_arg_plain_let_block");
}

#[test]
fn liar3_nested_spec_assert_false_is_refused() {
    expect_c3_error_containing(
        "l3_nested_spec_assert_false",
        &[NESTED_SPEC_ASSERTION_REFUSAL],
    );
}

#[test]
fn liar3_nested_plain_assert_false_is_refused() {
    expect_c3_error_containing(
        "l3_nested_plain_assert_false",
        &[NESTED_SPEC_ASSERTION_REFUSAL],
    );
}

#[test]
fn liar3_nested_spec_assert_after_write_is_refused() {
    expect_c3_error_containing(
        "l3_nested_spec_assert_after_write",
        &[NESTED_SPEC_ASSERTION_REFUSAL],
    );
}

#[test]
fn liar3_local_macro_tail_if_fails_closed() {
    expect_c3_poisoned("l3_local_macro_tail_if", "x");
}

#[test]
fn liar3_local_macro_tail_while_fails_closed() {
    expect_c3_poisoned("l3_local_macro_tail_while", "x");
}

#[test]
fn liar3_return_local_macro_tail_if_fails_closed() {
    expect_c3_poisoned("l3_return_local_macro_tail_if", "x");
}

#[test]
fn liar3_local_macro_tail_match_param_fails_closed() {
    expect_c3_poisoned("l3_local_macro_tail_match_param", "x");
}

#[test]
fn liar3_mut_self_autoref_value_block_is_refuted() {
    expect_c3_counterexample("l3_mut_self_autoref_value_block");
}

#[test]
fn liar3_mut_self_autoref_assert_arg_is_refuted() {
    expect_c3_counterexample("l3_mut_self_autoref_assert_arg");
}

#[test]
fn liar3_mut_binding_autoref_assert_arg_axiom_is_dropped() {
    expect_c3_error_containing(
        "l3_mut_binding_autoref_assert_arg",
        &["unknown return type for function 'helper_mut_binding'"],
    );
}

#[test]
fn liar3_mut_self_autoref_plain_is_refuted() {
    expect_c3_counterexample("l3_mut_self_autoref_plain");
}

#[test]
fn liar3_local_struct_field_autoref_fails_closed() {
    expect_c3_poisoned("l3_local_struct_field_autoref", "s");
}

#[test]
fn liar3_local_struct_field_autoref_value_block_fails_closed() {
    expect_c3_poisoned("l3_local_struct_field_autoref_value_block", "s");
}

#[test]
fn liar3_tuple_field_autoref_fails_closed() {
    expect_c3_poisoned("l3_tuple_field_autoref", "p");
}

#[test]
fn liar3_if_region_field_autoref_fails_closed() {
    expect_c3_poisoned("l3_if_region_field_autoref", "s");
}

#[test]
fn liar3_if_region_assert_arg_write_fails_closed() {
    expect_c3_error_containing(
        "l3_if_region_assert_arg_write",
        &[ASSERTION_OPERAND_STATEMENT_REFUSAL],
    );
}

#[test]
fn liar3_loop_assert_arg_write_is_refused() {
    expect_c3_error_containing(
        "l3_loop_assert_arg_write",
        &[ASSERTION_OPERAND_STATEMENT_REFUSAL],
    );
}

#[test]
fn liar3_helper_value_block_join_axiom_axiom_is_dropped() {
    expect_c3_error_containing(
        "l3_helper_value_block_join_axiom",
        &["unknown return type for function 'helper_block_join'"],
    );
}

#[test]
fn control3_projected_clone_verifies() {
    expect_c3_verified("c3_projected_clone");
}

#[test]
fn gated3_projected_count_ones_local_struct_fails_closed() {
    expect_c3_poisoned("g3_projected_count_ones_local_struct", "s");
}

#[test]
fn gated3_projected_count_ones_tuple_fails_closed() {
    expect_c3_poisoned("g3_projected_count_ones_tuple", "p");
}

// ============================================================================
// Cluster rank 4 — closure-captured writes and pure-name shadows
// ============================================================================

fn verify_c4(func: &str) -> VerifyResult {
    verify(&format!("c4_{func}"), func, SRC_C4)
}

fn expect_c4_verified(func: &str) {
    match verify_c4(func) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

/// Fail-closed error containing every needle (a liar or a gated true claim).
fn expect_c4_error_containing(func: &str, needles: &[&str]) {
    match verify_c4(func) {
        VerifyResult::Error { message } if needles.iter().all(|n| message.contains(n)) => {}
        other => {
            panic!("{func}: expected the fail-closed error containing {needles:?}, got {other:?}")
        }
    }
}

fn expect_c4_poisoned(func: &str, var: &str) {
    let unresolved = format!("unresolved variable `{var}`");
    expect_c4_error_containing(func, &[&unresolved, POISON_NOTE]);
}

fn expect_c4_closure_loop_refused(func: &str, var: &str) {
    let refusal = format!(
        "a closure inside a loop body writes the captured `{var}`, and the loop frame does not \
         havoc a closure capture; this is unsupported in vc_extraction"
    );
    expect_c4_error_containing(func, &[&refusal]);
}

fn expect_c4_shadow_refused(func: &str, method: &str, self_ty: &str) {
    let refusal = format!(
        "a call to `.{method}(..)` may resolve to the `&mut self` method `{method}` this file \
         implements for `{self_ty}`, which shadows the pure read vc_extraction assumes for that \
         name; this is unsupported in vc_extraction"
    );
    expect_c4_error_containing(func, &[&refusal]);
}

fn expect_c4_typed_receiver_refused(func: &str, method: &str, origin: &str) {
    let refusal = format!(
        "a call to `.{method}(..)` may resolve to the method `{method}` this file declares for \
         `{origin}` with a typed `&mut` receiver, which the receiver-kind registry does not \
         classify as mutating; this is unsupported in vc_extraction"
    );
    expect_c4_error_containing(func, &[&refusal]);
}

const SRC_C4: &str = r#"
use std::ops::AddAssign;

struct S4 {
    a: u64,
}

fn call_it<F: FnMut()>(mut f: F) {
    f();
}

trait Grab {
    fn get(&mut self, i: usize) -> u64;
}

impl Grab for Vec<u64> {
    fn get(&mut self, i: usize) -> u64 {
        self.push(7u64);
        i as u64
    }
}

trait Look {
    fn contains(&mut self, k: u64) -> bool;
}

impl Look for Vec<u64> {
    fn contains(&mut self, k: u64) -> bool {
        k == 0u64
    }
}

trait Bump {
    fn abs(&mut self) -> u64;
}

impl Bump for u64 {
    fn abs(&mut self) -> u64 {
        *self = *self + 1u64;
        *self
    }
}

struct W4 {
    x: u64,
}

impl W4 {
    fn get(&self) -> u64 {
        self.x
    }
}

trait Tick4 {
    fn tick(&mut self);
}

struct T4 {
    a: u64,
}

impl Tick4 for T4 {
    fn tick(&mut self) {
        self.a = self.a + 1u64;
    }
}

trait Peek4 {
    fn first(&mut self) -> u64;
}

impl<T: Tick4> Peek4 for T {
    fn first(&mut self) -> u64 {
        self.tick();
        0u64
    }
}

trait Cnt4 {
    fn count(&mut self) -> u64;
}

impl Cnt4 for [u64; 2] {
    fn count(&mut self) -> u64 {
        self[0] = self[0] + 1u64;
        0u64
    }
}

struct R4 {
    x: u64,
}

impl R4 {
    fn bump(self: &mut Self) {
        self.x = self.x + 1u64;
    }

    fn peek(self: &mut Self) -> u64 {
        self.x
    }
}

// ---- closure-captured writes inside a region ----------------------------------

// LIAR: panics at b = true (v == 3).
fn l4_iife_then(b: bool) {
    let mut v = 0u64;
    if b {
        (|| {
            v = 3u64;
        })();
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = false.
fn l4_iife_else(b: bool) {
    let mut v = 0u64;
    if b {
    } else {
        (|| {
            v = 3u64;
        })();
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true.
fn l4_iife_match_arm(b: bool) {
    let mut v = 0u64;
    match b {
        true => {
            (|| {
                v = 3u64;
            })();
        }
        false => {}
    }
    assert!(v == 0u64);
}

// LIAR: always panics.
fn l4_iife_plain_block() {
    let mut v = 0u64;
    {
        (|| {
            v = 3u64;
        })();
    }
    assert!(v == 0u64);
}

// LIAR: always panics.
#[allow(unused_unsafe)]
fn l4_iife_unsafe_block() {
    let mut v = 0u64;
    unsafe {
        (|| {
            v = 3u64;
        })();
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true.
fn l4_iife_compound_then(b: bool) {
    let mut v = 0u64;
    if b {
        (|| {
            v += 3u64;
        })();
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true (brace-less closure body).
fn l4_iife_bare_assign_then(b: bool) {
    let mut v = 0u64;
    if b {
        (|| v = 3u64)();
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true (closure bound and called inside the branch).
fn l4_closure_bound_in_then(b: bool) {
    let mut v = 0u64;
    if b {
        let mut c = || {
            v = 3u64;
        };
        c();
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true (closure bound in a block, called in a branch).
fn l4_closure_called_in_then(b: bool) {
    let mut v = 0u64;
    {
        let mut c = || {
            v = 3u64;
        };
        if b {
            c();
        }
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true (closure passed to a call).
fn l4_closure_passed_in_then(b: bool) {
    let mut v = 0u64;
    if b {
        call_it(|| {
            v = 3u64;
        });
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true (field of a captured struct).
fn l4_iife_field_then(b: bool) {
    let mut s = S4 { a: 0u64 };
    if b {
        (|| {
            s.a = 3u64;
        })();
    }
    assert!(s.a == 0u64);
}

// LIAR: panics at b = true (nested closure).
fn l4_nested_iife_then(b: bool) {
    let mut v = 0u64;
    if b {
        (|| {
            (|| {
                v = 3u64;
            })();
        })();
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true (value-position `if`).
fn l4_iife_value_if(b: bool) {
    let mut v = 0u64;
    let _y = if b {
        (|| {
            v = 3u64;
        })();
        1u64
    } else {
        2u64
    };
    assert!(v == 0u64);
}

// LIAR: panics at b = true (match guard).
fn l4_iife_match_guard(b: bool) {
    let mut v = 0u64;
    match b {
        true if {
            (|| {
                v = 3u64;
            })();
            true
        } => {}
        _ => {}
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true, v = 0 (declared `mut` parameter).
#[trust_vc::requires(v == 0u64)]
fn l4_iife_param_then(b: bool, mut v: u64) {
    if b {
        (|| {
            v = 3u64;
        })();
    }
    assert!(v == 0u64);
}

// LIAR: panics at b = true (branch inside a value block).
fn l4_iife_value_block_then(b: bool) {
    let mut v = 0u64;
    let _r = {
        if b {
            (|| {
                v = 3u64;
            })();
        }
        1u64
    };
    assert!(v == 0u64);
}

// LIAR: returns 3 at b = true.
#[trust_vc::ensures(result == 0u64)]
fn l4_iife_then_ensures(b: bool) -> u64 {
    let mut v = 0u64;
    if b {
        (|| {
            v = 3u64;
        })();
    }
    v
}

// ---- closure-captured writes inside a loop body -------------------------------

// LIAR: always panics.
fn l4_iife_while() {
    let mut v = 0u64;
    let mut i = 0u64;
    while i < 1u64 {
        (|| {
            v = 3u64;
        })();
        i = i + 1u64;
    }
    assert!(v == 0u64);
}

// LIAR: invariant `v == 0u64` fails at the second iteration head (n = 2).
fn l4_iife_invariant_loop(n: u64) {
    let mut v = 0u64;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(v == 0u64);
        (|| {
            v = 3u64;
        })();
        i = i + 1u64;
    }
}

// LIAR: same, closure passed to a call.
fn l4_closure_passed_invariant_loop(n: u64) {
    let mut v = 0u64;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(v == 0u64);
        call_it(|| {
            v = 3u64;
        });
        i = i + 1u64;
    }
}

// LIAR: same, closure bound in the body.
fn l4_closure_bound_invariant_loop(n: u64) {
    let mut v = 0u64;
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(v == 0u64);
        let mut c = || {
            v = 3u64;
        };
        c();
        i = i + 1u64;
    }
}

// ---- autoref / method members already closed by the rank-2/3 poison ----------

// LIAR (member 5): panics at b = true.
fn l4_add_assign_then(b: bool) {
    let mut x = 18u64;
    if b {
        x.add_assign(9u64);
    }
    assert!(x == 18u64);
}

// LIAR (member 5): always panics.
fn l4_add_assign_while() {
    let mut x = 18u64;
    let mut i = 0u64;
    while i < 1u64 {
        x.add_assign(9u64);
        i = i + 1u64;
    }
    assert!(x == 18u64);
}

// LIAR (member 5): always panics.
fn l4_add_assign_closure() {
    let mut x = 18u64;
    let mut c = || {
        x.add_assign(9u64);
    };
    c();
    assert!(x == 18u64);
}

// LIAR (member o1): panics at b = true.
fn l4_option_take_then(b: bool) {
    let mut o: Option<u64> = Some(3u64);
    if b {
        let _t = o.take();
    }
    assert!(o.is_some());
}

// LIAR (member 14): panics at b = true.
fn l4_user_trait_abs_then(b: bool) {
    let mut x = 0u64;
    if b {
        let _q: u64 = x.abs();
    }
    assert!(x == 0u64);
}

// LIAR (member c05k): panics at b = true, x = 0.
#[trust_vc::requires(x == 0u64)]
fn l4_add_assign_param_then(b: bool, mut x: u64) {
    if b {
        x.add_assign(1u64);
    }
    assert!(x == 0u64);
}

// LIAR (member 16): always panics (value block).
fn l4_add_assign_value_block() {
    let mut v = 0u64;
    let x = {
        v.add_assign(3u64);
        v
    };
    assert!(x == 0u64);
}

// ---- pure-name shadow: `impl Grab for Vec<u64> { fn get(&mut self, ..) }` ----

// LIAR: panics at b = true (`v.get` is `Grab::get`, which pushes).
fn l4_vec_get_shadow_then(b: bool) {
    let mut v: Vec<u64> = Vec::new();
    if b {
        let _k = v.get(0usize);
    }
    assert!(v.len() == 0usize);
}

// LIAR: invariant fails at the second iteration head (n = 2).
fn l4_vec_get_shadow_loop(n: usize) {
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(v.len() == 0usize);
        let _k = v.get(i);
        i = i + 1usize;
    }
}

// LIAR: always panics (declared parameter, straight line).
fn l4_vec_get_shadow_param(mut v: Vec<u64>) {
    let n = v.len();
    let _k = v.get(0usize);
    assert!(v.len() == n);
}

// LIAR: always panics (value block).
fn l4_vec_get_shadow_value_block(mut v: Vec<u64>) {
    let n = v.len();
    let _y = {
        let _k = v.get(0usize);
        1u64
    };
    assert!(v.len() == n);
}

// LIAR: panics at b = true (a blanket `impl<T: Tick4> Peek4 for T` gives the
// struct a `&mut self` `first` the receiver-kind registry does not key by `T4`).
fn l4_blanket_first_struct_then(b: bool) {
    let mut s = T4 { a: 0u64 };
    if b {
        let _k = s.first();
    }
    assert!(s.a == 0u64);
}

// LIAR: panics at b = true, s.a = 0 (declared parameter).
#[trust_vc::requires(s.a == 0u64)]
fn l4_blanket_first_struct_param_then(b: bool, mut s: T4) {
    if b {
        let _k = s.first();
    }
    assert!(s.a == 0u64);
}

// LIAR: panics at b = true (`impl Cnt4 for [u64; 2]`).
fn l4_array_count_shadow_then(b: bool) {
    let mut a = [0u64, 0u64];
    if b {
        let _k = a.count();
    }
    assert!(a[0usize] == 0u64);
}

// LIAR: always panics at a = [0, 0] (declared parameter, straight line).
#[trust_vc::requires(a[0usize] == 0u64)]
fn l4_array_count_shadow_param(mut a: [u64; 2]) {
    let _k = a.count();
    assert!(a[0usize] == 0u64);
}

// ---- typed `&mut` receiver: the registry reads `self: &mut Self` as by-value --

// LIAR: panics at b = true.
fn l4_typed_receiver_then(b: bool) {
    let mut r = R4 { x: 0u64 };
    if b {
        r.bump();
    }
    assert!(r.x == 0u64);
}

// LIAR: always panics at r.x = 0 (declared parameter, straight line).
#[trust_vc::requires(r.x == 0u64)]
fn l4_typed_receiver_param(mut r: R4) {
    r.bump();
    assert!(r.x == 0u64);
}

// LIAR: invariant fails at the second iteration head (n = 2, r.x = 0).
#[trust_vc::requires(r.x == 0u64)]
fn l4_typed_receiver_param_loop(n: u64, mut r: R4) {
    let mut i = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        trust_vc::invariant!(r.x == 0u64);
        r.bump();
        i = i + 1u64;
    }
}

// ---- controls ---------------------------------------------------------------

// CONTROL: the closure writes a branch-local, not a capture from outside.
fn c4_iife_writes_branch_local(b: bool) {
    let v = 0u64;
    if b {
        let mut w = 1u64;
        (|| {
            w = 3u64;
        })();
    }
    assert!(v == 0u64);
}

// CONTROL: the closure writes its own parameter.
fn c4_closure_writes_own_param(b: bool) {
    let v = 0u64;
    if b {
        let _z = (|mut z: u64| {
            z = 3u64;
            z
        })(1u64);
    }
    assert!(v == 0u64);
}

// CONTROL: a read-only closure in an invariant loop.
fn c4_read_only_closure_loop(n: u64) {
    let v = 5u64;
    let mut i = 0u64;
    let mut s = 0u64;
    while i < n {
        trust_vc::invariant!(i <= n);
        let c = || v;
        s = c();
        i = i + 1u64;
    }
    assert!(v == 5u64);
}

// CONTROL: the closure's capture is not the name the assertion reads.
fn c4_iife_unrelated_read(b: bool) {
    let mut v = 0u64;
    let w = 7u64;
    if b {
        (|| {
            v = 3u64;
        })();
    }
    assert!(w == 7u64);
}

// CONTROL: `len` is not shadowed; only `get` / `contains` are.
#[trust_vc::requires(v.len() == 0usize)]
fn c4_vec_len_not_shadowed(b: bool, v: Vec<u64>) {
    if b {
        let _n = v.len();
    }
    assert!(v.len() == 0usize);
}

// CONTROL: a struct receiver the registry resolves by type (`W4::get(&self)`).
// True at run time, but refused: the file implements a trait `get` for
// `Vec<u64>`, and the method-call rule reads method names, not receivers.
fn c4_struct_get_resolved_by_type(w: W4) {
    let _g = w.get();
    assert!(w.x == w.x);
}

// ---- gated (runtime-true, now refused) ---------------------------------------

// GATED: a `move` closure writes its own copy of `v`.
fn g4_move_iife_then(b: bool) {
    let mut v = 0u64;
    if b {
        (move || {
            v = 3u64;
            let _ = v;
        })();
    }
    assert!(v == 0u64);
}

// GATED: the closure writes the value `v` already holds.
fn g4_iife_same_value_then(b: bool) {
    let mut v = 0u64;
    if b {
        (|| {
            v = 0u64;
        })();
    }
    assert!(v == 0u64);
}

// GATED: same, in a loop.
fn g4_iife_same_value_while() {
    let mut v = 0u64;
    let mut i = 0u64;
    while i < 1u64 {
        (|| {
            v = 0u64;
        })();
        i = i + 1u64;
    }
    assert!(v == 0u64);
}

// GATED: `Look::contains` takes `&mut self` but writes nothing.
fn g4_vec_contains_shadow_non_mutating(b: bool) {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    if b {
        let _k = v.contains(1u64);
    }
    assert!(v.len() == 1usize);
}

// GATED: `R4::peek` takes a typed `&mut` receiver but writes nothing.
#[trust_vc::requires(r.x == 0u64)]
fn g4_typed_receiver_peek_param(mut r: R4) {
    let _k = r.peek();
    assert!(r.x == 0u64);
}
"#;

#[test]
fn liar4_iife_then_fails_closed() {
    expect_c4_poisoned("l4_iife_then", "v");
}

#[test]
fn liar4_iife_else_fails_closed() {
    expect_c4_poisoned("l4_iife_else", "v");
}

#[test]
fn liar4_iife_match_arm_fails_closed() {
    expect_c4_poisoned("l4_iife_match_arm", "v");
}

#[test]
fn liar4_iife_plain_block_fails_closed() {
    expect_c4_poisoned("l4_iife_plain_block", "v");
}

#[test]
fn liar4_iife_unsafe_block_fails_closed() {
    expect_c4_poisoned("l4_iife_unsafe_block", "v");
}

#[test]
fn liar4_iife_compound_then_fails_closed() {
    expect_c4_poisoned("l4_iife_compound_then", "v");
}

#[test]
fn liar4_iife_bare_assign_then_fails_closed() {
    expect_c4_poisoned("l4_iife_bare_assign_then", "v");
}

#[test]
fn liar4_closure_bound_in_then_fails_closed() {
    expect_c4_poisoned("l4_closure_bound_in_then", "v");
}

#[test]
fn liar4_closure_called_in_then_fails_closed() {
    expect_c4_poisoned("l4_closure_called_in_then", "v");
}

#[test]
fn liar4_closure_passed_in_then_fails_closed() {
    expect_c4_poisoned("l4_closure_passed_in_then", "v");
}

#[test]
fn liar4_iife_field_then_fails_closed() {
    expect_c4_poisoned("l4_iife_field_then", "s");
}

#[test]
fn liar4_nested_iife_then_fails_closed() {
    expect_c4_poisoned("l4_nested_iife_then", "v");
}

#[test]
fn liar4_iife_value_if_fails_closed() {
    expect_c4_poisoned("l4_iife_value_if", "v");
}

#[test]
fn liar4_iife_match_guard_fails_closed() {
    expect_c4_poisoned("l4_iife_match_guard", "v");
}

#[test]
fn liar4_iife_param_then_fails_closed() {
    expect_c4_poisoned("l4_iife_param_then", "v");
}

#[test]
fn liar4_iife_value_block_then_fails_closed() {
    expect_c4_poisoned("l4_iife_value_block_then", "v");
}

#[test]
fn liar4_iife_then_ensures_fails_closed() {
    expect_c4_poisoned("l4_iife_then_ensures", "v");
}

#[test]
fn liar4_iife_while_is_refused() {
    expect_c4_closure_loop_refused("l4_iife_while", "v");
}

#[test]
fn liar4_iife_invariant_loop_is_refused() {
    expect_c4_closure_loop_refused("l4_iife_invariant_loop", "v");
}

#[test]
fn liar4_closure_passed_invariant_loop_is_refused() {
    expect_c4_closure_loop_refused("l4_closure_passed_invariant_loop", "v");
}

#[test]
fn liar4_closure_bound_invariant_loop_is_refused() {
    expect_c4_closure_loop_refused("l4_closure_bound_invariant_loop", "v");
}

#[test]
fn liar4_add_assign_then_fails_closed() {
    expect_c4_poisoned("l4_add_assign_then", "x");
}

#[test]
fn liar4_add_assign_closure_fails_closed() {
    expect_c4_poisoned("l4_add_assign_closure", "x");
}

#[test]
fn liar4_option_take_then_fails_closed() {
    expect_c4_poisoned("l4_option_take_then", "o");
}

#[test]
fn liar4_user_trait_abs_then_fails_closed() {
    expect_c4_poisoned("l4_user_trait_abs_then", "x");
}

#[test]
fn liar4_add_assign_param_then_fails_closed() {
    expect_c4_poisoned("l4_add_assign_param_then", "x");
}

#[test]
fn liar4_add_assign_value_block_fails_closed() {
    expect_c4_poisoned("l4_add_assign_value_block", "v");
}

#[test]
fn liar4_add_assign_while_is_refused() {
    expect_c4_error_containing("l4_add_assign_while", &[LOOP_METHOD_REFUSAL]);
}

#[test]
fn liar4_blanket_first_struct_then_is_refused() {
    expect_c4_shadow_refused("l4_blanket_first_struct_then", "first", "T");
}

#[test]
fn liar4_blanket_first_struct_param_then_is_refused() {
    expect_c4_shadow_refused("l4_blanket_first_struct_param_then", "first", "T");
}

#[test]
fn liar4_array_count_shadow_then_is_refused() {
    expect_c4_shadow_refused("l4_array_count_shadow_then", "count", "[u64 ; 2]");
}

#[test]
fn liar4_array_count_shadow_param_is_refused() {
    expect_c4_shadow_refused("l4_array_count_shadow_param", "count", "[u64 ; 2]");
}

#[test]
fn liar4_vec_get_shadow_then_is_refused() {
    expect_c4_shadow_refused("l4_vec_get_shadow_then", "get", "Vec < u64 >");
}

#[test]
fn liar4_vec_get_shadow_loop_is_refused() {
    expect_c4_shadow_refused("l4_vec_get_shadow_loop", "get", "Vec < u64 >");
}

#[test]
fn liar4_vec_get_shadow_param_is_refused() {
    expect_c4_shadow_refused("l4_vec_get_shadow_param", "get", "Vec < u64 >");
}

#[test]
fn liar4_vec_get_shadow_value_block_is_refused() {
    expect_c4_shadow_refused("l4_vec_get_shadow_value_block", "get", "Vec < u64 >");
}

#[test]
fn control4_iife_writes_branch_local_verifies() {
    expect_c4_verified("c4_iife_writes_branch_local");
}

#[test]
fn control4_closure_writes_own_param_verifies() {
    expect_c4_verified("c4_closure_writes_own_param");
}

#[test]
fn control4_read_only_closure_loop_verifies() {
    expect_c4_verified("c4_read_only_closure_loop");
}

#[test]
fn control4_iife_unrelated_read_verifies() {
    expect_c4_verified("c4_iife_unrelated_read");
}

#[test]
fn control4_vec_len_not_shadowed_verifies() {
    expect_c4_verified("c4_vec_len_not_shadowed");
}

/// The shadow refusal above lets this call through by its receiver's type;
/// the method-call rule refuses the `Verified` answer it would give, since
/// `Grab::get` is implemented for `Vec<u64>` in the same file.
#[test]
fn control4_struct_get_beside_a_vec_trait_get_is_refused_by_name() {
    expect_c4_error_containing(
        "c4_struct_get_resolved_by_type",
        &[
            "trait method resolution",
            "`get` is a method of the trait `Grab`",
        ],
    );
}

#[test]
fn gated4_move_iife_then_fails_closed() {
    expect_c4_poisoned("g4_move_iife_then", "v");
}

#[test]
fn gated4_iife_same_value_then_fails_closed() {
    expect_c4_poisoned("g4_iife_same_value_then", "v");
}

#[test]
fn gated4_iife_same_value_while_is_refused() {
    expect_c4_closure_loop_refused("g4_iife_same_value_while", "v");
}

#[test]
fn gated4_vec_contains_shadow_non_mutating_is_refused() {
    expect_c4_shadow_refused(
        "g4_vec_contains_shadow_non_mutating",
        "contains",
        "Vec < u64 >",
    );
}

#[test]
fn liar4_typed_receiver_then_is_refused() {
    expect_c4_typed_receiver_refused("l4_typed_receiver_then", "bump", "R4");
}

#[test]
fn liar4_typed_receiver_param_is_refused() {
    expect_c4_typed_receiver_refused("l4_typed_receiver_param", "bump", "R4");
}

#[test]
fn liar4_typed_receiver_param_loop_is_refused() {
    expect_c4_typed_receiver_refused("l4_typed_receiver_param_loop", "bump", "R4");
}

#[test]
fn gated4_typed_receiver_peek_param_is_refused() {
    expect_c4_typed_receiver_refused("g4_typed_receiver_peek_param", "peek", "R4");
}

// ============================================================================
// Cluster rank 5 — integer literal width lost
// ============================================================================

fn verify_c5(func: &str) -> VerifyResult {
    verify(&format!("c5_{func}"), func, SRC_C5)
}

fn expect_c5_verified(func: &str) {
    match verify_c5(func) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

/// A liar refuted once the literal carries its width: a Counterexample whose
/// obligation names `fragment`.
fn expect_c5_counterexample_on(func: &str, fragment: &str) {
    match verify_c5(func) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.contains(fragment) => {}
        other => panic!("{func}: expected a Counterexample naming {fragment:?}, got {other:?}"),
    }
}

/// A liar whose overflow the solver now finds but reports without a model
/// (`Unknown`, EmptyModel): pinned only as never `Verified`.
fn expect_c5_not_verified(func: &str) {
    let result = verify_c5(func);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{func}: must never be Verified, got {result:?}"
    );
}

fn expect_c5_literal_value_refused(func: &str, ty: &str, rhs: &str) {
    let refusal = format!(
        "an unsuffixed integer literal value written to a `{ty}` binding is unsupported in \
         vc_extraction unless it is a single literal: `{rhs}`"
    );
    match verify_c5(func) {
        VerifyResult::Error { message } if message.contains(&refusal) => {}
        other => panic!("{func}: expected the fail-closed error {refusal:?}, got {other:?}"),
    }
}

const SRC_C5: &str = r#"
// ---- (a) an unsuffixed literal written to a typed binding ----

// Witness: none (constants). Runtime: `x + 10` on 250u8 panics.
#[trust_vc::ensures(true)]
fn l5_assign_lit_then_add() {
    let mut x: u8 = 0u8;
    x = 250;
    x = x + 10;
    assert!(x > 255u8);
}

#[trust_vc::ensures(true)]
fn l5_assign_lit_through_alias() {
    let mut x: u8 = 0u8;
    let r = &mut x;
    *r = 250;
    *r = *r + 10;
    assert!(*r > 255u8);
}

// Witness: x = 0.
#[trust_vc::ensures(true)]
fn l5_assign_lit_mut_param(mut x: u8) {
    x = 250;
    x = x + 10;
}

#[trust_vc::ensures(true)]
fn l5_assign_zero_then_sub() {
    let mut x: u8 = 5u8;
    x = 0;
    x = x - 1;
}

#[trust_vc::ensures(true)]
fn l5_deferred_init_then_add() {
    let mut x: u8;
    x = 250;
    x = x + 10;
}

#[trust_vc::ensures(true)]
fn l5_assign_lit_then_compound() {
    let mut x: u8 = 0u8;
    x = 250;
    x += 10;
}

#[trust_vc::ensures(true)]
fn l5_assign_lit_then_shl() {
    let mut x: u8 = 0u8;
    x = 1;
    x = x << 9u32;
}

#[trust_vc::ensures(true)]
fn l5_assign_u32_max_then_add() {
    let mut x: u32 = 0u32;
    x = 4294967295;
    x = x + 1;
}

#[trust_vc::ensures(true)]
fn l5_assign_lit_in_block() {
    let mut x: u8 = 0u8;
    {
        x = 250;
        x = x + 10;
    }
}

#[trust_vc::ensures(true)]
fn l5_assign_lit_in_loop() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 1u8 {
        trust_vc::invariant!(i <= 1u8);
        x = 250;
        x = x + 10;
        i = i + 1u8;
    }
}

#[trust_vc::ensures(true)]
fn l5_suffix_inferred_local() {
    let mut x = 5u8;
    x = 250;
    x = x + 10;
}

#[trust_vc::ensures(true)]
fn l5_assign_paren_lit() {
    let mut x: u8 = 0u8;
    x = (250);
    x = x + 10;
}

#[trust_vc::ensures(true)]
fn l5_assign_composite_lit() {
    let mut x: u8 = 0u8;
    x = 200 + 50;
    x = x + 10;
}

// Witness: b = true and b = false.
#[trust_vc::ensures(true)]
fn l5_assign_if_lit_value(b: bool) {
    let mut x: u8 = 0u8;
    x = if b { 250 } else { 250 };
    x = x + 10;
}

#[trust_vc::ensures(true)]
fn l5_assign_block_lit_value() {
    let mut x: u8 = 0u8;
    x = { 250 };
    x = x + 10;
}

#[trust_vc::ensures(true)]
fn l5_let_composite_lit() {
    let mut x: u8 = 200 + 50;
    x = x + 10;
}

#[trust_vc::ensures(true)]
fn l5_let_negative_lit() {
    let mut x: i8 = -128;
    x = x - 1;
}

#[trust_vc::ensures(true)]
fn l5_assign_negative_lit() {
    let mut x: i8 = 0i8;
    x = -128;
    x = x - 1;
}

// ---- (b) closed i32-literal arithmetic beside a narrower variable ----

// Witness: a = 2.
#[trust_vc::requires(a == 2i8)]
fn l5_i32_mul_beside_i8(a: i8) {
    let r0: i32 = 21i32 * 21i32;
    assert!(r0 != 441i32);
}

#[trust_vc::requires(a == 2i8)]
fn l5_i32_add_beside_i8(a: i8) {
    let r0: i32 = 100i32 + 100i32;
    assert!(r0 != 200i32);
}

#[trust_vc::requires(a == 2i8)]
fn l5_i32_let_operands_beside_i8(a: i8) {
    let f3: i32 = 31i32 - 10i32;
    let mut r0: i32 = 0i32;
    r0 = f3 * f3;
    assert!(r0 != 441i32);
}

#[trust_vc::requires(a == 2i8)]
fn l5_unsuffixed_mul_beside_i8(a: i8) {
    let r0 = 21 * 21;
    assert!(r0 != 441);
}

#[trust_vc::requires(a == 2i8)]
fn l5_direct_i32_sum_beside_i8(a: i8) {
    assert!(100i32 + 100i32 < 0i32);
}

#[trust_vc::requires(a == 2i8)]
fn l5_i32_negated_sum_beside_i8(a: i8) {
    let r: i32 = -(100i32 + 100i32);
    assert!(r != -200i32);
}

#[trust_vc::requires(a == 2i8)]
fn l5_i32_min_div_beside_i8(a: i8) {
    let r: i32 = -128i32 / -1i32;
    assert!(r != 128i32);
}

// Witness: a = 2.
#[trust_vc::requires(a == 2u8)]
fn l5_unsuffixed_mul_beside_u8(a: u8) {
    let r: i32 = 20 * 20;
    assert!(r != 400);
}

// ---- controls ----

#[trust_vc::ensures(true)]
fn c5_assign_lit_in_range() {
    let mut x: u8 = 0u8;
    x = 250;
    x = x + 5;
    assert!(x == 255u8);
}

#[trust_vc::ensures(true)]
fn c5_assign_lit_through_alias_in_range() {
    let mut x: u8 = 0u8;
    let r = &mut x;
    *r = 250;
    *r = *r + 5;
    assert!(*r == 255u8);
}

// Witness: x = 0 and x = 255.
#[trust_vc::ensures(true)]
fn c5_untyped_shadow_of_u8_param(x: u8) {
    let mut x = 0;
    x = 250;
    x = x + 10;
    assert!(x == 260);
}

#[trust_vc::ensures(true)]
fn c5_assign_lit_i32_local() {
    let mut x: i32 = 0i32;
    x = 250;
    x = x + 10;
    assert!(x == 260i32);
}

#[trust_vc::ensures(true)]
fn c5_assign_zero_then_add() {
    let mut x: u8 = 5u8;
    x = 0;
    x = x + 1;
    assert!(x == 1u8);
}

// Witness: x = 0 and x = 255.
#[trust_vc::ensures(true)]
fn c5_assign_lit_mut_param_in_range(mut x: u8) {
    x = 250;
    assert!(x == 250u8);
}

#[trust_vc::requires(a == 2i8)]
fn c5_i32_mul_beside_i8_true(a: i8) {
    let r0: i32 = 21i32 * 21i32;
    assert!(r0 == 441i32);
}

#[trust_vc::requires(a == 2i8)]
fn c5_small_i32_mul_beside_i8(a: i8) {
    let r0: i32 = 3i32 * 3i32;
    assert!(r0 == 9i32);
}

#[trust_vc::requires(a == 2u8)]
fn c5_u8_below_literal_product(a: u8) {
    assert!(a < 2 * 3);
}

// ---- gated: runtime-true, now refused ----

#[trust_vc::ensures(true)]
fn g5_assign_composite_lit_in_range() {
    let mut x: u8 = 0u8;
    x = 200 + 50;
    assert!(x == 250u8);
}

// Witness: b = true and b = false.
#[trust_vc::ensures(true)]
fn g5_let_if_lit_value(b: bool) {
    let x: u64 = if b { 1 } else { 0 };
    assert!(x <= 1u64);
}

#[trust_vc::ensures(true)]
fn g5_let_composite_lit_in_range() {
    let x: u8 = 200 + 50;
    assert!(x == 250u8);
}
"#;

#[test]
fn liar5_assign_lit_then_add_is_refuted() {
    expect_c5_counterexample_on("l5_assign_lit_then_add", "addition overflow");
}

#[test]
fn liar5_assign_lit_through_alias_is_refuted() {
    expect_c5_counterexample_on("l5_assign_lit_through_alias", "addition overflow");
}

#[test]
fn liar5_assign_lit_mut_param_is_refuted() {
    expect_c5_counterexample_on("l5_assign_lit_mut_param", "addition overflow");
}

#[test]
fn liar5_assign_zero_then_sub_is_refuted() {
    expect_c5_counterexample_on("l5_assign_zero_then_sub", "subtraction overflow");
}

#[test]
fn liar5_deferred_init_then_add_is_refuted() {
    expect_c5_counterexample_on("l5_deferred_init_then_add", "addition overflow");
}

#[test]
fn liar5_assign_lit_then_compound_is_refuted() {
    expect_c5_counterexample_on("l5_assign_lit_then_compound", "addition overflow");
}

#[test]
fn liar5_assign_lit_then_shl_is_refuted() {
    expect_c5_counterexample_on("l5_assign_lit_then_shl", "left shift overflow");
}

#[test]
fn liar5_assign_u32_max_then_add_is_refuted() {
    expect_c5_counterexample_on("l5_assign_u32_max_then_add", "addition overflow");
}

#[test]
fn liar5_assign_lit_in_block_is_refuted() {
    expect_c5_counterexample_on("l5_assign_lit_in_block", "addition overflow");
}

#[test]
fn liar5_assign_lit_in_loop_is_refuted() {
    expect_c5_counterexample_on("l5_assign_lit_in_loop", "addition overflow");
}

#[test]
fn liar5_suffix_inferred_local_is_refuted() {
    expect_c5_counterexample_on("l5_suffix_inferred_local", "addition overflow");
}

#[test]
fn liar5_assign_paren_lit_is_refuted() {
    expect_c5_counterexample_on("l5_assign_paren_lit", "addition overflow");
}

#[test]
fn liar5_assign_composite_lit_is_refused() {
    expect_c5_literal_value_refused("l5_assign_composite_lit", "u8", "200 + 50");
}

#[test]
fn liar5_assign_if_lit_value_is_refused() {
    expect_c5_literal_value_refused("l5_assign_if_lit_value", "u8", "if b { 250 } else { 250 }");
}

#[test]
fn liar5_assign_block_lit_value_is_refused() {
    expect_c5_literal_value_refused("l5_assign_block_lit_value", "u8", "{ 250 }");
}

#[test]
fn liar5_let_composite_lit_is_refused() {
    expect_c5_literal_value_refused("l5_let_composite_lit", "u8", "200 + 50");
}

#[test]
fn liar5_let_negative_lit_is_not_verified() {
    expect_c5_not_verified("l5_let_negative_lit");
}

#[test]
fn liar5_assign_negative_lit_is_not_verified() {
    expect_c5_not_verified("l5_assign_negative_lit");
}

#[test]
fn liar5_i32_mul_beside_i8_is_refuted() {
    expect_c5_counterexample_on("l5_i32_mul_beside_i8", "assertion");
}

#[test]
fn liar5_i32_add_beside_i8_is_refuted() {
    expect_c5_counterexample_on("l5_i32_add_beside_i8", "assertion");
}

#[test]
fn liar5_i32_let_operands_beside_i8_is_refuted() {
    expect_c5_counterexample_on("l5_i32_let_operands_beside_i8", "assertion");
}

#[test]
fn liar5_unsuffixed_mul_beside_i8_is_refuted() {
    expect_c5_counterexample_on("l5_unsuffixed_mul_beside_i8", "assertion");
}

#[test]
fn liar5_direct_i32_sum_beside_i8_is_refuted() {
    expect_c5_counterexample_on("l5_direct_i32_sum_beside_i8", "assertion");
}

#[test]
fn liar5_i32_negated_sum_beside_i8_is_refuted() {
    expect_c5_counterexample_on("l5_i32_negated_sum_beside_i8", "assertion");
}

#[test]
fn liar5_i32_min_div_beside_i8_is_refuted() {
    expect_c5_counterexample_on("l5_i32_min_div_beside_i8", "assertion");
}

#[test]
fn liar5_unsuffixed_mul_beside_u8_is_refuted() {
    expect_c5_counterexample_on("l5_unsuffixed_mul_beside_u8", "assertion");
}

#[test]
fn control5_assign_lit_in_range_verifies() {
    expect_c5_verified("c5_assign_lit_in_range");
}

#[test]
fn control5_assign_lit_through_alias_in_range_verifies() {
    expect_c5_verified("c5_assign_lit_through_alias_in_range");
}

#[test]
fn control5_untyped_shadow_of_u8_param_verifies() {
    expect_c5_verified("c5_untyped_shadow_of_u8_param");
}

#[test]
fn control5_assign_lit_i32_local_verifies() {
    expect_c5_verified("c5_assign_lit_i32_local");
}

#[test]
fn control5_assign_zero_then_add_verifies() {
    expect_c5_verified("c5_assign_zero_then_add");
}

#[test]
fn control5_assign_lit_mut_param_in_range_verifies() {
    expect_c5_verified("c5_assign_lit_mut_param_in_range");
}

#[test]
fn control5_i32_mul_beside_i8_true_verifies() {
    expect_c5_verified("c5_i32_mul_beside_i8_true");
}

#[test]
fn control5_small_i32_mul_beside_i8_verifies() {
    expect_c5_verified("c5_small_i32_mul_beside_i8");
}

#[test]
fn control5_u8_below_literal_product_verifies() {
    expect_c5_verified("c5_u8_below_literal_product");
}

#[test]
fn gated5_assign_composite_lit_in_range_is_refused() {
    expect_c5_literal_value_refused("g5_assign_composite_lit_in_range", "u8", "200 + 50");
}

#[test]
fn gated5_let_if_lit_value_is_refused() {
    expect_c5_literal_value_refused("g5_let_if_lit_value", "u64", "if b { 1 } else { 0 }");
}

#[test]
fn gated5_let_composite_lit_in_range_is_refused() {
    expect_c5_literal_value_refused("g5_let_composite_lit_in_range", "u8", "200 + 50");
}

// ============================================================================
// Cluster rank 6 — `#[cfg]` never evaluated
// ============================================================================

fn verify_c6(func: &str, src: &str) -> VerifyResult {
    verify(&format!("c6_{func}"), func, src)
}

fn expect_c6_verified(func: &str, src: &str) {
    match verify_c6(func, src) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

/// The body refusal: a `cfg` / `cfg_attr` attribute inside the function.
fn expect_c6_body_cfg_refused(func: &str, src: &str) {
    let refusal = format!(
        "a `#[cfg]` / `#[cfg_attr]` attribute in `{func}` is not evaluated by vc_extraction, so \
         a statement, item or definition it compiles out would be modeled as present; this is \
         unsupported in vc_extraction"
    );
    match verify_c6(func, src) {
        VerifyResult::Error { message } if message.contains(&refusal) => {}
        other => panic!("{func}: expected the fail-closed error {refusal:?}, got {other:?}"),
    }
}

/// The file refusal: `name` reaches a declaration that carries a `cfg`.
fn expect_c6_file_cfg_refused(func: &str, src: &str, name: &str) {
    let refusal = format!(
        "`{name}` reaches a declaration in this file that carries a `#[cfg]` / `#[cfg_attr]` \
         attribute; vc_extraction does not evaluate `cfg`, so it may read a compiled-out \
         definition; this is unsupported in vc_extraction"
    );
    match verify_c6(func, src) {
        VerifyResult::Error { message } if message.contains(&refusal) => {}
        other => panic!("{func}: expected the fail-closed error {refusal:?}, got {other:?}"),
    }
}

const SRC_C6: &str = r#"
// ---- (7) a cfg-gated statement modeled as running ----

// LIAR member 7. Witness: b = true.
#[trust_vc::ensures(true)]
fn l6_cfg_if(b: bool) {
    let mut x = 0u64;
    #[cfg(any())]
    if b {
        x = 5u64;
    }
    assert!(!b || x == 5u64);
}

// LIAR c07d.
#[trust_vc::ensures(true)]
fn l6_cfg_let_shadow() {
    let x: u64 = 1u64;
    #[cfg(any())]
    let x: u64 = 2u64;
    assert!(x == 2u64);
}

// LIAR: the compiled-out statement was consumed as an assumption. Witness: x = 0.
#[trust_vc::ensures(true)]
fn l6_cfg_assume_stmt(x: u64) {
    #[cfg(any())]
    trust_vc::assume!(x == 5u64);
    assert!(x == 5u64);
}

// LIAR.
#[trust_vc::ensures(true)]
fn l6_cfg_push_stmt() {
    let mut v: Vec<u64> = Vec::new();
    #[cfg(any())]
    v.push(1u64);
    assert!(v.len() == 1usize);
}

// LIAR.
#[trust_vc::ensures(true)]
fn l6_cfg_let_block_shadow() {
    let x: u64 = 1u64;
    #[cfg(any())]
    let x = { 2u64 };
    assert!(x == 2u64);
}

// LIAR. Witness: b = true.
#[trust_vc::ensures(true)]
fn l6_cfg_branch_if(b: bool) {
    let mut x = 0u64;
    if b {
        #[cfg(any())]
        if true {
            x = 5u64;
        }
    }
    assert!(!b || x == 5u64);
}

// LIAR: the compiled-out `let` hid the overflow. Witness: n = 255.
#[trust_vc::ensures(true)]
fn l6_cfg_let_hides_overflow(n: u8) {
    #[cfg(any())]
    let n = 0u8;
    let _m = n + 1u8;
}

// LIAR. Witness: n = 0.
#[trust_vc::ensures(true)]
fn l6_cfg_let_shadows_param(n: u8) {
    #[cfg(any())]
    let n: u8 = 3u8;
    assert!(n == 3u8);
}

// LIAR: the function returns 1.
#[trust_vc::ensures(result == 2u64)]
fn l6_cfg_let_before_tail() -> u64 {
    let x = 1u64;
    #[cfg(any())]
    let x = 2u64;
    x
}

// GATED: runtime-true (`all()` is always set).
#[trust_vc::ensures(true)]
fn g6_cfg_all_if(b: bool) {
    let mut x = 0u64;
    #[cfg(all())]
    if b {
        x = 5u64;
    }
    assert!(!b || x == 5u64);
}

// GATED: runtime-true (the gated item is unused).
#[trust_vc::ensures(true)]
fn g6_cfg_nested_unused_const() {
    const K: u64 = 1u64;
    #[cfg(any())]
    const K2: u64 = 2u64;
    assert!(K == 1u64);
}

// CONTROL: a `cfg_attr` carrying only a lint attribute compiles nothing out.
#[trust_vc::ensures(true)]
fn c6_cfg_attr_allow_if(b: bool) {
    let mut x = 0u64;
    #[cfg_attr(any(), allow(unused))]
    if b {
        x = 5u64;
    }
    assert!(!b || x == 5u64);
}

// CONTROL: the same on the function itself.
#[cfg_attr(test, allow(unused_variables))]
#[trust_vc::ensures(true)]
fn c6_cfg_attr_allow_fn(x: u64) {
    let y = 3u64;
    assert!(y == 3u64);
}

// CONTROL: the ungated neighbour of member 7.
#[trust_vc::ensures(true)]
fn c6_plain_if(b: bool) {
    let mut x = 0u64;
    if b {
        x = 5u64;
    }
    assert!(!b || x == 5u64);
}
"#;

// ---- (22) a file-level cfg-selected definition: the first one was taken ----

const SRC_C6_CONST: &str = r#"
#[cfg(any())]
const K: u64 = 1u64;
#[cfg(not(any()))]
const K: u64 = 2u64;

// LIAR member 22: the compiled `K` is 2.
#[trust_vc::ensures(true)]
fn l6_cfg_selected_const() {
    let mut x = 0u64;
    x = K;
    assert!(x == 1u64);
}

// LIAR: returns 2.
#[trust_vc::ensures(result == 1u64)]
fn l6_cfg_selected_const_result() -> u64 {
    let mut x = 0u64;
    x = K;
    x
}

// LIAR: the precondition admits n = 1 (witness).
#[trust_vc::requires(n < K)]
#[trust_vc::ensures(true)]
fn l6_cfg_selected_const_requires(n: u64) {
    let m = n;
    assert!(m < 1u64);
}

// CONTROL: a function that reaches no cfg-carrying declaration.
#[trust_vc::ensures(true)]
fn c6_unrelated_beside_cfg_const() {
    let x = 3u64;
    assert!(x == 3u64);
}
"#;

const SRC_C6_CONST_SWAPPED: &str = r#"
#[cfg(not(any()))]
const K: u64 = 2u64;
#[cfg(any())]
const K: u64 = 1u64;

// GATED: runtime-true (the live definition happens to be the first).
#[trust_vc::ensures(true)]
fn g6_cfg_selected_const_swapped() {
    let mut x = 0u64;
    x = K;
    assert!(x == 2u64);
}
"#;

const SRC_C6_TARGET_DUP: &str = r#"
// LIAR: the verified name resolved to the compiled-out definition; the live one
// asserts `false`.
#[cfg(any())]
#[trust_vc::ensures(true)]
fn l6_cfg_selected_target() {}
#[cfg(not(any()))]
#[trust_vc::ensures(true)]
fn l6_cfg_selected_target() {
    assert!(false);
}
"#;

const SRC_C6_TEST_MOD: &str = r#"
const K: u64 = 2u64;
#[cfg(any())]
const Z: u64 = 9u64;

fn noisy() -> u64 {
    #[cfg(debug_assertions)]
    let _y = 1u64;
    3u64
}

// CONTROL: an unrelated `#[cfg(test)] mod tests`, an unreached cfg const and an
// unreached helper with a cfg statement do not trip the refusal.
#[trust_vc::ensures(true)]
fn c6_test_mod_const_read() {
    let mut x = 0u64;
    x = K;
    assert!(x == 2u64);
}

// CONTROL: a name the test module calls is not tainted by it.
#[trust_vc::ensures(result == 5u64)]
fn c6_test_mod_called_fn() -> u64 {
    5u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t() {
        assert!(c6_test_mod_called_fn() == 5);
    }

    // CONTROL: a function verified inside the cfg-gated module is the
    // definition asked for; its own declaration does not taint its name.
    #[trust_vc::ensures(result == 3u64)]
    fn c6_inside_test_mod() -> u64 {
        let x = 3u64;
        x
    }
}
"#;

const SRC_C6_TEST_MOD_SHADOW: &str = r#"
const K: u64 = 2u64;

// GATED: runtime-true; the test module declares its own `K`, which the refusal
// counts as a cfg-carrying declaration of the name.
#[trust_vc::ensures(true)]
fn g6_test_mod_redeclares_const() {
    let mut x = 0u64;
    x = K;
    assert!(x == 2u64);
}

#[cfg(test)]
mod tests {
    const K: u64 = 9u64;

    #[test]
    fn t() {
        assert!(K == 9);
    }
}
"#;

#[test]
fn liar6_cfg_if_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_if", SRC_C6);
}

#[test]
fn liar6_cfg_let_shadow_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_let_shadow", SRC_C6);
}

#[test]
fn liar6_cfg_assume_stmt_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_assume_stmt", SRC_C6);
}

#[test]
fn liar6_cfg_push_stmt_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_push_stmt", SRC_C6);
}

#[test]
fn liar6_cfg_let_block_shadow_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_let_block_shadow", SRC_C6);
}

#[test]
fn liar6_cfg_branch_if_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_branch_if", SRC_C6);
}

#[test]
fn liar6_cfg_let_hides_overflow_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_let_hides_overflow", SRC_C6);
}

#[test]
fn liar6_cfg_let_shadows_param_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_let_shadows_param", SRC_C6);
}

#[test]
fn liar6_cfg_let_before_tail_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_let_before_tail", SRC_C6);
}

#[test]
fn liar6_cfg_selected_const_is_refused() {
    expect_c6_file_cfg_refused("l6_cfg_selected_const", SRC_C6_CONST, "K");
}

#[test]
fn liar6_cfg_selected_const_result_is_refused() {
    expect_c6_file_cfg_refused("l6_cfg_selected_const_result", SRC_C6_CONST, "K");
}

#[test]
fn liar6_cfg_selected_const_requires_is_refused() {
    expect_c6_file_cfg_refused("l6_cfg_selected_const_requires", SRC_C6_CONST, "K");
}

#[test]
fn liar6_cfg_selected_target_is_refused() {
    expect_c6_body_cfg_refused("l6_cfg_selected_target", SRC_C6_TARGET_DUP);
}

#[test]
fn control6_cfg_attr_allow_if_verifies() {
    expect_c6_verified("c6_cfg_attr_allow_if", SRC_C6);
}

#[test]
fn control6_cfg_attr_allow_fn_verifies() {
    expect_c6_verified("c6_cfg_attr_allow_fn", SRC_C6);
}

#[test]
fn control6_plain_if_verifies() {
    expect_c6_verified("c6_plain_if", SRC_C6);
}

#[test]
fn control6_unrelated_beside_cfg_const_verifies() {
    expect_c6_verified("c6_unrelated_beside_cfg_const", SRC_C6_CONST);
}

#[test]
fn control6_test_mod_const_read_verifies() {
    expect_c6_verified("c6_test_mod_const_read", SRC_C6_TEST_MOD);
}

#[test]
fn control6_test_mod_called_fn_verifies() {
    expect_c6_verified("c6_test_mod_called_fn", SRC_C6_TEST_MOD);
}

#[test]
fn control6_inside_test_mod_verifies() {
    expect_c6_verified("c6_inside_test_mod", SRC_C6_TEST_MOD);
}

#[test]
fn gated6_cfg_all_if_is_refused() {
    expect_c6_body_cfg_refused("g6_cfg_all_if", SRC_C6);
}

#[test]
fn gated6_cfg_nested_unused_const_is_refused() {
    expect_c6_body_cfg_refused("g6_cfg_nested_unused_const", SRC_C6);
}

#[test]
fn gated6_cfg_selected_const_swapped_is_refused() {
    expect_c6_file_cfg_refused("g6_cfg_selected_const_swapped", SRC_C6_CONST_SWAPPED, "K");
}

#[test]
fn gated6_test_mod_redeclares_const_is_refused() {
    expect_c6_file_cfg_refused("g6_test_mod_redeclares_const", SRC_C6_TEST_MOD_SHADOW, "K");
}

// ============================================================================
// Review round 1 — regressions of ranks 1 and 5, and nine pre-existing holes
// ============================================================================

fn verify_r1(func: &str, src: &str) -> VerifyResult {
    verify(&format!("r1_{func}"), func, src)
}

fn expect_r1_verified(func: &str, src: &str) {
    match verify_r1(func, src) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_r1_counterexample(func: &str, src: &str) {
    match verify_r1(func, src) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

fn expect_r1_counterexample_on(func: &str, src: &str, fragment: &str) {
    match verify_r1(func, src) {
        VerifyResult::Counterexample {
            obligation_name, ..
        } if obligation_name.contains(fragment) => {}
        other => panic!("{func}: expected a Counterexample naming {fragment:?}, got {other:?}"),
    }
}

fn expect_r1_error_containing(func: &str, src: &str, needles: &[&str]) {
    match verify_r1(func, src) {
        VerifyResult::Error { message } if needles.iter().all(|n| message.contains(n)) => {}
        other => {
            panic!("{func}: expected the fail-closed error containing {needles:?}, got {other:?}")
        }
    }
}

const WHILE_COND_REFUSAL: &str = "the condition of this `while` loop may change";
const SHADOW_REFUSAL: &str = "which shadows the pure read vc_extraction assumes for that name";
const MACRO_SHADOW_ORIGIN: &str = "a macro expansion in this file";

// ---- rank-5 introduced regression: closed literal tree beside a narrow operand ----

const SRC_R1_LIT: &str = r#"#![allow(arithmetic_overflow)]
#![allow(unused)]

// ---- introduced regression (a): closed literal tree beside a narrow operand ----

// LIAR: panics at z = 100 (u8 add overflow).
#[trust_vc::ensures(true)]
fn lr_lit_u8_typed_let(z: u8) {
    let _w: u8 = z + (100 + 100);
}

// LIAR: panics at z = 100.
#[trust_vc::ensures(true)]
fn lr_lit_u8_untyped_let(z: u8) {
    let _w = z + (100 + 100);
}

// LIAR: panics at z = 64.
#[trust_vc::ensures(true)]
fn lr_lit_u8_mul(z: u8) {
    let _w: u8 = z * (2 + 2);
}

// LIAR: panics at z = 101 (subtract overflow).
#[trust_vc::ensures(true)]
fn lr_lit_u8_sub(z: u8) {
    let _w: u8 = (100 + 100) - z - z;
}

// LIAR: panics at z = 100 (i8).
#[trust_vc::ensures(true)]
fn lr_lit_i8_add(z: i8) {
    let _w: i8 = z + (50 + 50);
}

// LIAR: panics at z = 1000 (i16).
#[trust_vc::ensures(true)]
fn lr_lit_i16_add(z: i16) {
    let _w: i16 = z + (20000 + 20000);
}

// LIAR: panics at z = 10000 (u16).
#[trust_vc::ensures(true)]
fn lr_lit_u16_add(z: u16) {
    let _w: u16 = z + (30000 + 30000);
}

// LIAR: panics at z = 100 (assignment form).
#[trust_vc::ensures(true)]
fn lr_lit_assign(z: u8) {
    let mut w: u8 = 0u8;
    w = z + (100 + 100);
}

// LIAR: panics at z = 100 (compound form).
#[trust_vc::ensures(true)]
fn lr_lit_compound(z: u8) {
    let mut w: u8 = z;
    w += 100 + 100;
}

// LIAR: panics at z = 100 (return lane).
#[trust_vc::ensures(result == 0u8)]
fn lr_lit_ret_zero(z: u8) -> u8 {
    z + (100 + 100) - z - 200
}

// LIAR: panics at z = 100.
#[trust_vc::ensures(result <= 255u8)]
fn lr_lit_ret_le(z: u8) -> u8 {
    z + (100 + 100)
}

// LIAR: panics at z = 100, b = true.
#[trust_vc::ensures(true)]
fn lr_lit_if_value(z: u8, b: bool) {
    let _w: u8 = if b { z + (100 + 100) } else { 0u8 };
}

// LIAR: panics at z = 100 (loop body).
#[trust_vc::ensures(true)]
fn lr_lit_loop(z: u8) {
    let mut acc: u8 = z;
    let mut i: u8 = 0u8;
    while i < 1u8 {
        acc = acc + (100 + 100);
        i = i + 1u8;
    }
}

// LIAR: panics at z = 100 (nested closed trees).
#[trust_vc::ensures(true)]
fn lr_lit_nested_closed(z: u8) {
    let _w: u8 = z + ((50 + 50) + (50 + 50));
}

// LIAR: panics at z = 64 (closed tree on the left).
#[trust_vc::ensures(true)]
fn lr_lit_left_closed(z: u8) {
    let _w: u8 = (2 * 2) * z;
}

// LIAR: panics at z = -128 (i8 negation times MIN).
#[trust_vc::requires(z == -128i8)]
#[trust_vc::ensures(true)]
fn lr_lit_i8_neg_mul(z: i8) {
    let _w: i8 = -(1 + 1) * z;
}

// LIAR: the assertion's own arithmetic overflows at z = 100.
#[trust_vc::ensures(true)]
fn lr_lit_spec(z: u8) {
    assert!(z + (100 + 100) != 255u8 || true);
}

// ---- introduced regression (b): closed literal tree compared to a narrow variable ----

// LIAR: `100 + 100` is i8 arithmetic here; panics at y = 0.
#[trust_vc::ensures(true)]
fn lr_lit_cmp_let_bool(y: i8) {
    let t: bool = y == 100 + 100;
    assert!(!t);
}

// LIAR: panics at y = 0.
#[trust_vc::ensures(true)]
fn lr_lit_cmp_if_cond(y: i8) {
    let mut w: u64 = 0u64;
    if y == 100 + 100 {
        w = 1u64;
    }
    assert!(w == 0u64);
}

// LIAR: panics at y = 0.
#[trust_vc::ensures(true)]
fn lr_lit_cmp_assert_ne(y: i8) {
    assert!(y != 100 + 100);
}

// LIAR: panics at y = 0.
#[trust_vc::ensures(true)]
fn lr_lit_cmp_assert_ne_mul(y: i8) {
    assert!(y != 16 * 16);
}

// LIAR: panics at y = 0.
#[trust_vc::ensures(true)]
fn lr_lit_cmp_assert_ne_neg(y: i8) {
    assert!(y != -(100 + 100));
}

// LIAR: panics at y = 0.
#[trust_vc::ensures(true)]
fn lr_lit_cmp_assert_ne_subchain(y: i8) {
    assert!(y != 0 - 100 - 100);
}

// LIAR: panics at y = 0 (u16).
#[trust_vc::ensures(true)]
fn lr_lit_cmp_assert_ne_u16(y: u16) {
    assert!(y != 300 * 300);
}

// ---- closed literal tree beside a NON-scalar narrow operand (pre-existing at HEAD) ----

// LIAR: panics at a[0] = 100 (index operand).
#[trust_vc::requires(a[0usize] == 100u8)]
#[trust_vc::ensures(true)]
fn lr_lit_index_plus_closed(a: [u8; 2]) {
    let _w: u8 = a[0usize] + (100 + 100);
}

// LIAR: panics at z = 100 (cast operand).
#[trust_vc::requires(z == 100u32)]
#[trust_vc::ensures(true)]
fn lr_lit_cast_plus_closed(z: u32) {
    let _w: u8 = (z as u8) + (100 + 100);
}

// LIAR: panics at z = 100 (bitwise closed tree, 0xF0 & 0xFF = 240).
#[trust_vc::requires(z == 100u8)]
#[trust_vc::ensures(true)]
fn lr_lit_hex_closed(z: u8) {
    let _w: u8 = z + (0xF0 & 0xFF);
}

// LIAR: `200 + 100` is u8 arithmetic; panics at y = 0.
#[trust_vc::ensures(true)]
fn lr_lit_cmp_assert_ne_sum_u8(y: u8) {
    assert!(y != 200 + 100);
}

// LIAR: panics at y = 0.
#[trust_vc::ensures(true)]
fn lr_lit_cmp_lt_sum_u8(y: u8) {
    assert!(y < 200 + 100);
}

// CONTROL: the same shape in range stays Verified.
#[trust_vc::requires(z <= 55u8)]
#[trust_vc::ensures(true)]
fn cr_lit_u8_closed_in_range(z: u8) {
    let _w: u8 = z + (100 + 100);
}

// CONTROL: an in-range closed comparison stays Verified.
#[trust_vc::requires(y == 3i8)]
#[trust_vc::ensures(true)]
fn cr_lit_cmp_i8_in_range(y: i8) {
    assert!(y != 50 + 50);
}

// CONTROL (rank-5 member 31 stays closed): the i32 product is 441, not BV8 185.
#[trust_vc::requires(a == 2i8)]
fn cr_lit_i32_mul_beside_i8_true(a: i8) {
    let r0: i32 = 21i32 * 21i32;
    assert!(r0 == 441i32);
}
"#;

#[test]
fn liar_r1_lit_u8_typed_let_is_refuted() {
    expect_r1_counterexample_on("lr_lit_u8_typed_let", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_u8_untyped_let_is_refuted() {
    expect_r1_counterexample_on("lr_lit_u8_untyped_let", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_u8_mul_is_refuted() {
    expect_r1_counterexample_on("lr_lit_u8_mul", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_u8_sub_is_refuted() {
    expect_r1_counterexample_on("lr_lit_u8_sub", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_i8_add_is_refuted() {
    expect_r1_counterexample_on("lr_lit_i8_add", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_i16_add_is_refuted() {
    expect_r1_counterexample_on("lr_lit_i16_add", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_u16_add_is_refuted() {
    expect_r1_counterexample_on("lr_lit_u16_add", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_assign_is_refuted() {
    expect_r1_counterexample_on("lr_lit_assign", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_compound_is_refuted() {
    expect_r1_counterexample_on("lr_lit_compound", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_ret_zero_is_refuted() {
    expect_r1_counterexample_on("lr_lit_ret_zero", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_ret_le_is_refuted() {
    expect_r1_counterexample_on("lr_lit_ret_le", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_if_value_is_refuted() {
    expect_r1_counterexample_on("lr_lit_if_value", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_loop_is_refuted() {
    expect_r1_counterexample_on("lr_lit_loop", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_nested_closed_is_refuted() {
    expect_r1_counterexample_on("lr_lit_nested_closed", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_left_closed_is_refuted() {
    expect_r1_counterexample_on("lr_lit_left_closed", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_i8_neg_mul_is_refuted() {
    expect_r1_counterexample_on("lr_lit_i8_neg_mul", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_index_plus_closed_is_refuted() {
    expect_r1_counterexample_on("lr_lit_index_plus_closed", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_cast_plus_closed_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cast_plus_closed", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_hex_closed_is_refuted() {
    expect_r1_counterexample_on("lr_lit_hex_closed", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_spec_is_refuted() {
    expect_r1_counterexample_on("lr_lit_spec", SRC_R1_LIT, "assertion");
}

// The `i8` addition panics where the comparison is evaluated, before the
// assertion that reads its result: the comparison's operand is a panic-safety
// site typed by its peer `y` (§5b rule 2), whose obligation is the first one
// refuted.
#[test]
fn liar_r1_lit_cmp_let_bool_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_let_bool", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_cmp_if_cond_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_if_cond", SRC_R1_LIT, "overflow_check");
}

#[test]
fn liar_r1_lit_cmp_assert_ne_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_assert_ne", SRC_R1_LIT, "assertion");
}

#[test]
fn liar_r1_lit_cmp_assert_ne_mul_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_assert_ne_mul", SRC_R1_LIT, "assertion");
}

#[test]
fn liar_r1_lit_cmp_assert_ne_neg_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_assert_ne_neg", SRC_R1_LIT, "assertion");
}

#[test]
fn liar_r1_lit_cmp_assert_ne_subchain_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_assert_ne_subchain", SRC_R1_LIT, "assertion");
}

#[test]
fn liar_r1_lit_cmp_assert_ne_u16_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_assert_ne_u16", SRC_R1_LIT, "assertion");
}

#[test]
fn liar_r1_lit_cmp_assert_ne_sum_u8_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_assert_ne_sum_u8", SRC_R1_LIT, "assertion");
}

#[test]
fn liar_r1_lit_cmp_lt_sum_u8_is_refuted() {
    expect_r1_counterexample_on("lr_lit_cmp_lt_sum_u8", SRC_R1_LIT, "assertion");
}

#[test]
fn control_r1_lit_u8_closed_in_range_verifies() {
    expect_r1_verified("cr_lit_u8_closed_in_range", SRC_R1_LIT);
}

#[test]
fn control_r1_lit_cmp_i8_in_range_verifies() {
    expect_r1_verified("cr_lit_cmp_i8_in_range", SRC_R1_LIT);
}

#[test]
fn control_r1_lit_i32_mul_beside_i8_true_verifies() {
    expect_r1_verified("cr_lit_i32_mul_beside_i8_true", SRC_R1_LIT);
}

// ---- rank-1 introduced regression F1: projected compound havoc refuted true claims ----

const SRC_R1_F1: &str = r#"#![allow(unused)]

struct Acc {
    total: u64,
    count: u64,
}
struct Pl {
    f: u8,
    g: u16,
}
struct W {
    p: Pl,
    q: u64,
}

// GATED (runtime-true; HEAD Verified; the rank-1 havoc REFUTED it): the
// sibling field's own overflow check after a bounded compound.
#[trust_vc::requires(a.total < 100u64 && a.count == 0u64)]
#[trust_vc::ensures(true)]
fn gr_f1_param_struct_two_fields(mut a: Acc) {
    a.total += 1u64;
    a.count = a.count + 1u64;
}

// GATED: `&mut` parameter twin.
#[trust_vc::requires(r.total < 10u64 && r.count < 10u64)]
#[trust_vc::ensures(true)]
fn gr_f1_mut_ref_two_fields(r: &mut Acc) {
    r.total += 1u64;
    r.count += 1u64;
}

// GATED: a sibling-field read after a bounded compound.
#[trust_vc::requires(s.f < 10u8 && s.g == 7u16)]
#[trust_vc::ensures(true)]
fn gr_f1_sibling_field_read(mut s: Pl) {
    s.f += 1u8;
    assert!(s.g == 7u16);
}

// GATED: a postcondition over an untouched tuple field.
#[trust_vc::requires(x.0 > 0u64 && x.1 == 3u64)]
#[trust_vc::ensures(result == 4u64)]
fn gr_f1_untouched_tuple_field(mut x: (u64, u64)) -> u64 {
    x.0 -= 1u64;
    x.1 + 1u64
}

// GATED: the same field twice, both bounded.
#[trust_vc::requires(s.f < 10u8)]
#[trust_vc::ensures(true)]
fn gr_f1_same_field_twice(mut s: Pl) {
    s.f += 1u8;
    s.f += 1u8;
}

// GATED: a nested-field compound then a sibling read.
#[trust_vc::requires(w.p.f < 10u8 && w.q == 5u64)]
#[trust_vc::ensures(true)]
fn gr_f1_nested_field_sibling(mut w: W) {
    w.p.f += 1u8;
    assert!(w.q == 5u64);
}

// GATED: both arms compound, then a sibling read after the join.
#[trust_vc::requires(p.0 < 10u8 && p.1 == 3u8)]
#[trust_vc::ensures(true)]
fn gr_f1_branch_join_compound(mut p: (u8, u8), c: bool) {
    if c {
        p.0 ^= 1u8;
    } else {
        p.0 |= 1u8;
    }
    assert!(p.1 == 3u8);
}
"#;

#[test]
fn gated_r1_f1_param_struct_two_fields_fails_closed() {
    expect_r1_error_containing(
        "gr_f1_param_struct_two_fields",
        SRC_R1_F1,
        &[UNRESOLVED, "`a`"],
    );
}

#[test]
fn gated_r1_f1_mut_ref_two_fields_fails_closed() {
    expect_r1_error_containing("gr_f1_mut_ref_two_fields", SRC_R1_F1, &[UNRESOLVED, "`r`"]);
}

#[test]
fn gated_r1_f1_sibling_field_read_fails_closed() {
    expect_r1_error_containing("gr_f1_sibling_field_read", SRC_R1_F1, &[UNRESOLVED, "`s`"]);
}

#[test]
fn gated_r1_f1_untouched_tuple_field_fails_closed() {
    expect_r1_error_containing(
        "gr_f1_untouched_tuple_field",
        SRC_R1_F1,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn gated_r1_f1_same_field_twice_fails_closed() {
    expect_r1_error_containing("gr_f1_same_field_twice", SRC_R1_F1, &[UNRESOLVED, "`s`"]);
}

#[test]
fn gated_r1_f1_nested_field_sibling_fails_closed() {
    expect_r1_error_containing(
        "gr_f1_nested_field_sibling",
        SRC_R1_F1,
        &[UNRESOLVED, "`w`"],
    );
}

#[test]
fn gated_r1_f1_branch_join_compound_fails_closed() {
    expect_r1_error_containing(
        "gr_f1_branch_join_compound",
        SRC_R1_F1,
        &[UNRESOLVED, "`p`"],
    );
}

// ---- rank-1 introduced regression F2: new loop-body sites over havoc symbols ----

const SRC_R1_F2: &str = r#"#![allow(unused)]

struct Pl {
    f: u8,
    g: u16,
}

// GATED (runtime-true; HEAD Verified; the rank-1 site REFUTED it over
// `x__loopbody_N`): an `if let` scrutinee over a loop-modified operand.
#[trust_vc::ensures(true)]
fn gr_f2_iflet_loop() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        if let 0u8 = x + 1u8 {}
        x = 1u8;
        i += 1u8;
    }
}

// GATED: an index-assignment RHS over a loop-modified operand.
#[trust_vc::ensures(true)]
fn gr_f2_index_assign_loop() {
    let mut a: [u8; 10] = [0u8; 10];
    let mut last: u8 = 0u8;
    let mut i: usize = 0usize;
    while i < 10usize {
        a[i] = last + 1u8;
        last = 5u8;
        i += 1usize;
    }
}

// GATED: a field-assignment RHS over a loop-modified operand.
#[trust_vc::ensures(true)]
fn gr_f2_field_assign_loop() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    let mut last: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        s.f = last + 1u8;
        last = i;
        i += 1u8;
    }
}

// GATED: a nested `while let` scrutinee over an outer-loop-modified operand.
#[trust_vc::ensures(true)]
fn gr_f2_while_let_nested_loop() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        while let 0u8 = x + 1u8 {
            x = 1u8;
        }
        x = 1u8;
        i += 1u8;
    }
}

// GATED: the operand is the guard-bounded counter itself (a rank-1 control
// that the refusal now fails closed).
#[trust_vc::ensures(true)]
fn gr_f2_field_assign_guard_bounded() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    let mut i: u8 = 0u8;
    while i < 10u8 {
        s.f = i + 1u8;
        i += 1u8;
    }
}

// CONTROL: a loop-invariant operand renders exactly and stays Verified.
#[trust_vc::requires(n < 255u8)]
#[trust_vc::ensures(true)]
fn cr_f2_field_assign_param_operand(n: u8) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    let mut i: u8 = 0u8;
    while i < 10u8 {
        s.f = n + 1u8;
        i += 1u8;
    }
}

// CONTROL: `if let` scrutinee over a loop-invariant operand.
#[trust_vc::requires(n < 255u8)]
#[trust_vc::ensures(true)]
fn cr_f2_iflet_param_operand(n: u8) {
    let mut i: u8 = 0u8;
    while i < 10u8 {
        if let 0u8 = n + 1u8 {}
        i += 1u8;
    }
}

// CONTROL: no arithmetic / index site in the RHS, so nothing is refused.
#[trust_vc::ensures(true)]
fn cr_f2_field_assign_plain_modified() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        s.f = x;
        x = 1u8;
        i += 1u8;
    }
}

// LIAR: panics on the first iteration at n = 255 (exact operand, refuted).
#[trust_vc::requires(n == 255u8)]
#[trust_vc::ensures(true)]
fn lr_f2_field_assign_param_operand(n: u8) {
    let mut s = Pl { f: 0u8, g: 0u16 };
    let mut i: u8 = 0u8;
    while i < 10u8 {
        s.f = n + 1u8;
        i += 1u8;
    }
}

// LIAR: panics on the first iteration at n = 255.
#[trust_vc::requires(n == 255u8)]
#[trust_vc::ensures(true)]
fn lr_f2_iflet_param_operand(n: u8) {
    let mut i: u8 = 0u8;
    while i < 10u8 {
        if let 0u8 = n + 1u8 {}
        i += 1u8;
    }
}

// LIAR: panics on the second iteration (x = 255); the site is refused.
#[trust_vc::ensures(true)]
fn lr_f2_field_assign_modified_operand() {
    let mut s = Pl { f: 0u8, g: 0u16 };
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        s.f = x + 1u8;
        x = 255u8;
        i += 1u8;
    }
}

// LIAR: panics on the second iteration; the site is refused.
#[trust_vc::ensures(true)]
fn lr_f2_iflet_modified_operand() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        if let 0u8 = x + 1u8 {}
        x = 255u8;
        i += 1u8;
    }
}
"#;

#[test]
fn gated_r1_f2_iflet_loop_fails_closed() {
    expect_r1_error_containing(
        "gr_f2_iflet_loop",
        SRC_R1_F2,
        &[LOOP_HAVOC_SITE_REFUSAL, "`x + 1u8`"],
    );
}

#[test]
fn gated_r1_f2_index_assign_loop_fails_closed() {
    expect_r1_error_containing(
        "gr_f2_index_assign_loop",
        SRC_R1_F2,
        &[LOOP_HAVOC_SITE_REFUSAL, "`last + 1u8`"],
    );
}

#[test]
fn gated_r1_f2_field_assign_loop_fails_closed() {
    expect_r1_error_containing(
        "gr_f2_field_assign_loop",
        SRC_R1_F2,
        &[LOOP_HAVOC_SITE_REFUSAL, "`last + 1u8`"],
    );
}

#[test]
fn gated_r1_f2_while_let_nested_loop_fails_closed() {
    expect_r1_error_containing(
        "gr_f2_while_let_nested_loop",
        SRC_R1_F2,
        &[LOOP_HAVOC_SITE_REFUSAL, "`x + 1u8`"],
    );
}

#[test]
fn gated_r1_f2_field_assign_guard_bounded_fails_closed() {
    expect_r1_error_containing(
        "gr_f2_field_assign_guard_bounded",
        SRC_R1_F2,
        &[LOOP_HAVOC_SITE_REFUSAL, "`i + 1u8`"],
    );
}

#[test]
fn control_r1_f2_field_assign_param_operand_verifies() {
    expect_r1_verified("cr_f2_field_assign_param_operand", SRC_R1_F2);
}

#[test]
fn control_r1_f2_iflet_param_operand_verifies() {
    expect_r1_verified("cr_f2_iflet_param_operand", SRC_R1_F2);
}

#[test]
fn control_r1_f2_field_assign_plain_modified_verifies() {
    expect_r1_verified("cr_f2_field_assign_plain_modified", SRC_R1_F2);
}

#[test]
fn liar_r1_f2_field_assign_param_operand_is_refuted() {
    expect_r1_counterexample_on(
        "lr_f2_field_assign_param_operand",
        SRC_R1_F2,
        "overflow_check",
    );
}

#[test]
fn liar_r1_f2_iflet_param_operand_is_refuted() {
    expect_r1_counterexample_on("lr_f2_iflet_param_operand", SRC_R1_F2, "overflow_check");
}

#[test]
fn liar_r1_f2_field_assign_modified_operand_fails_closed() {
    expect_r1_error_containing(
        "lr_f2_field_assign_modified_operand",
        SRC_R1_F2,
        &[LOOP_HAVOC_SITE_REFUSAL, "`x + 1u8`"],
    );
}

#[test]
fn liar_r1_f2_iflet_modified_operand_fails_closed() {
    expect_r1_error_containing(
        "lr_f2_iflet_modified_operand",
        SRC_R1_F2,
        &[LOOP_HAVOC_SITE_REFUSAL, "`x + 1u8`"],
    );
}

// ---- pre-existing: unframed compound, effectful index, `while` condition effects ----

const SRC_R1_STATE: &str = r#"#![allow(unused)]
use std::ops::AddAssign;

// ---- compound assignment to a declared name that no scope frame binds ----

// LIAR: the assertion fails at x = 0 (x is 1).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound(mut x: u64) {
    x += 1u64;
    assert!(x == 0u64);
}

// LIAR: fails at x = 10.
#[trust_vc::requires(x == 10u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_sub(mut x: u64) {
    x -= 1u64;
    assert!(x == 10u64);
}

// LIAR: fails at x = 1.
#[trust_vc::requires(x == 1u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_shl(mut x: u64) {
    x <<= 1u64;
    assert!(x == 1u64);
}

// LIAR: returns 1 at x = 0.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(result == 0u64)]
fn lr_cmp_param_compound_return(mut x: u64) -> u64 {
    x += 1u64;
    x
}

// LIAR: divides by zero at x = 5.
#[trust_vc::requires(x == 5u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_div_zero(mut x: u64) {
    x -= 5u64;
    let _y = 10u64 / x;
}

// LIAR: indexes out of bounds at i = 0.
#[trust_vc::requires(i == 0usize)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_index(mut i: usize, a: [u8; 1]) {
    i += 1usize;
    let _y = a[i];
}

// LIAR: overflows at x = 10 (10 + 200 + 200).
#[trust_vc::requires(x == 10u8)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_overflow(mut x: u8) {
    x += 200u8;
    x += 200u8;
}

// LIAR: fails at x = 0 (block form).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_block(mut x: u64) {
    {
        x += 1u64;
    }
    assert!(x == 0u64);
}

// LIAR: fails at x = 0 (`unsafe` block).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_unsafe(mut x: u64) {
    unsafe {
        x += 1u64;
    }
    assert!(x == 0u64);
}

// LIAR: fails at x = 0 (value block).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_value_block(mut x: u64) {
    let _v: u64 = {
        x += 1u64;
        5u64
    };
    assert!(x == 0u64);
}

// LIAR: fails at x = 0 (copied out).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_copy(mut x: u64) {
    x += 1u64;
    let y = x;
    assert!(y == 0u64);
}

// LIAR: fails at x = 0 (twice).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_param_compound_twice(mut x: u64) {
    x += 1u64;
    x += 1u64;
    assert!(x == 0u64);
}

// LIAR: fails at x = 0 (RHS carries an assignment, on a rebound param).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_rebound_param_compound_rhs_assign(mut x: u64) {
    let mut y: u64 = 0u64;
    x = 0u64;
    x += {
        y = 1u64;
        y
    };
    assert!(x == 0u64);
}

// LIAR: fails always (the shadowing local is 8, the param is read).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_cmp_shadowing_let_compound(x: u64) {
    let mut y: u64 = 0u64;
    let mut x = 7u64;
    x += {
        y = 1u64;
        y
    };
    assert!(x == 0u64);
}

// GATED (runtime-true; HEAD Verified): the bounded claim after a param compound.
#[trust_vc::requires(x < 10u64)]
#[trust_vc::ensures(true)]
fn gr_cmp_param_compound_bound(mut x: u64) {
    x += 1u64;
    assert!(x <= 10u64);
}

// GATED (runtime-true; HEAD gave a SPURIOUS Counterexample because the read
// reverted to the entry symbol): the exact claim after a param compound.
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn gr_cmp_param_compound_true(mut x: u64) {
    x += 1u64;
    assert!(x == 1u64);
}

// CONTROL: a declared local compound is modeled and stays Verified.
#[trust_vc::ensures(true)]
fn cr_cmp_local_compound_true() {
    let mut x: u64 = 0u64;
    x += 1u64;
    assert!(x == 1u64);
}

// ---- index assignment whose index has a side effect ----

// LIAR: fails (a[0] is 5).
#[trust_vc::requires(a[0usize] == 0u8)]
#[trust_vc::ensures(true)]
fn lr_idx_effect_param(mut a: [u8; 2]) {
    let mut j: usize = 1usize;
    a[{
        j = 0usize;
        j
    }] = 5u8;
    assert!(a[0usize] == 0u8);
}

// LIAR: fails (a[1] is 5).
#[trust_vc::requires(a[1usize] == 0u8)]
#[trust_vc::ensures(true)]
fn lr_idx_effect_param_elem1(mut a: [u8; 2]) {
    let mut j: usize = 0usize;
    a[{
        j = 1usize;
        j
    }] = 5u8;
    assert!(a[1usize] == 0u8);
}

// LIAR: fails (the shadowing local's a[0] is 5; the parameter was read).
#[trust_vc::requires(a[0usize] == 9u8)]
#[trust_vc::ensures(true)]
fn lr_idx_effect_shadow(a: [u8; 2]) {
    let mut j: usize = 1usize;
    let mut a = [9u8, 9u8];
    a[{
        j = 0usize;
        j
    }] = 5u8;
    assert!(a[0usize] == 9u8);
}

// CONTROL: a plain index assignment stays modeled.
#[trust_vc::requires(a[0usize] == 0u8)]
#[trust_vc::ensures(true)]
fn cr_idx_plain(mut a: [u8; 2]) {
    a[0usize] = 5u8;
    assert!(a[0usize] == 5u8);
}

// ---- effects in a `while` condition / `while let` scrutinee ----

// LIAR: fails (v is empty after the loop).
#[trust_vc::ensures(true)]
fn lr_while_let_pop() {
    let mut v: Vec<u64> = vec![1u64, 2u64];
    while let Some(_e) = v.pop() {}
    assert!(v.len() == 2usize);
}

// LIAR: fails.
#[trust_vc::ensures(true)]
fn lr_while_pop_is_some() {
    let mut v: Vec<u64> = vec![1u64, 2u64];
    while v.pop().is_some() {}
    assert!(v.len() == 2usize);
}

// LIAR: fails at x = 0 (x is 1).
#[trust_vc::requires(x == 0u64)]
#[trust_vc::ensures(true)]
fn lr_while_cond_block_add_assign_param(mut x: u64) {
    while {
        x.add_assign(1u64);
        false
    } {}
    assert!(x == 0u64);
}

// LIAR: fails (x is 1). HEAD already refuted this plain-assignment twin.
#[trust_vc::ensures(true)]
fn lr_while_cond_block_assign_local() {
    let mut x: u64 = 0u64;
    while {
        x = 1u64;
        false
    } {}
    assert!(x == 0u64);
}

// LIAR: fails (v is 3).
#[trust_vc::ensures(true)]
fn lr_while_cond_closure_capture() {
    let mut v: u64 = 0u64;
    while {
        (|| {
            v = 3u64;
        })();
        false
    } {}
    assert!(v == 0u64);
}

// LIAR: fails (x is 1).
#[trust_vc::ensures(true)]
fn lr_while_cond_inner_if_write() {
    let mut x: u64 = 0u64;
    let b: bool = true;
    while {
        if b {
            x = 1u64;
        }
        false
    } {}
    assert!(x == 0u64);
}

// LIAR: fails (x is 1).
#[trust_vc::ensures(true)]
fn lr_while_cond_inner_block_write() {
    let mut x: u64 = 0u64;
    while {
        {
            x = 1u64;
        }
        false
    } {}
    assert!(x == 0u64);
}

// LIAR: fails (v.len() is 1).
#[trust_vc::ensures(true)]
fn lr_while_cond_push() {
    let mut v: Vec<u64> = Vec::new();
    while {
        v.push(1u64);
        false
    } {}
    assert!(v.len() == 0usize);
}

// LIAR: overflows at x = 250 (255 + 1).
#[trust_vc::requires(x == 250u8)]
#[trust_vc::ensures(true)]
fn lr_while_cond_add_assign_then_arith(mut x: u8) {
    while {
        x.add_assign(5u8);
        false
    } {}
    let _y: u8 = x + 1u8;
}

// CONTROL: a pure `while` condition is not refused.
#[trust_vc::ensures(true)]
fn cr_while_pure_cond() {
    let mut i: u64 = 0u64;
    while i < 3u64 {
        i = i + 1u64;
    }
    assert!(i >= 3u64);
}

// CONTROL: a pure `.len()` in the condition is not refused.
#[trust_vc::ensures(true)]
fn cr_while_len_cond(v: Vec<u64>) {
    let mut i: usize = 0usize;
    while i < v.len() {
        i = i + 1usize;
    }
}
"#;

#[test]
fn liar_r1_cmp_param_compound_fails_closed() {
    expect_r1_error_containing("lr_cmp_param_compound", SRC_R1_STATE, &[UNRESOLVED, "`x`"]);
}

#[test]
fn liar_r1_cmp_param_compound_sub_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_sub",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_shl_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_shl",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_return_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_return",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_div_zero_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_div_zero",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_index_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_index",
        SRC_R1_STATE,
        &[UNRESOLVED, "`i`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_overflow_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_overflow",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_block_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_block",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_unsafe_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_unsafe",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_value_block_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_value_block",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_copy_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_copy",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_param_compound_twice_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_param_compound_twice",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_rebound_param_compound_rhs_assign_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_rebound_param_compound_rhs_assign",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_cmp_shadowing_let_compound_fails_closed() {
    expect_r1_error_containing(
        "lr_cmp_shadowing_let_compound",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_idx_effect_param_fails_closed() {
    expect_r1_error_containing("lr_idx_effect_param", SRC_R1_STATE, &[UNRESOLVED, "`a`"]);
}

#[test]
fn liar_r1_idx_effect_param_elem1_fails_closed() {
    expect_r1_error_containing(
        "lr_idx_effect_param_elem1",
        SRC_R1_STATE,
        &[UNRESOLVED, "`a`"],
    );
}

#[test]
fn liar_r1_idx_effect_shadow_fails_closed() {
    expect_r1_error_containing("lr_idx_effect_shadow", SRC_R1_STATE, &[UNRESOLVED, "`a`"]);
}

#[test]
fn gated_r1_cmp_param_compound_bound_fails_closed() {
    expect_r1_error_containing(
        "gr_cmp_param_compound_bound",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn gated_r1_cmp_param_compound_true_fails_closed() {
    expect_r1_error_containing(
        "gr_cmp_param_compound_true",
        SRC_R1_STATE,
        &[UNRESOLVED, "`x`"],
    );
}

#[test]
fn liar_r1_while_let_pop_is_refused() {
    expect_r1_error_containing(
        "lr_while_let_pop",
        SRC_R1_STATE,
        &[WHILE_COND_REFUSAL, "`v`"],
    );
}

#[test]
fn liar_r1_while_pop_is_some_is_refused() {
    expect_r1_error_containing(
        "lr_while_pop_is_some",
        SRC_R1_STATE,
        &[WHILE_COND_REFUSAL, "`v`"],
    );
}

#[test]
fn liar_r1_while_cond_block_add_assign_param_is_refused() {
    expect_r1_error_containing(
        "lr_while_cond_block_add_assign_param",
        SRC_R1_STATE,
        &[WHILE_COND_REFUSAL, "`x`"],
    );
}

#[test]
fn liar_r1_while_cond_closure_capture_is_refused() {
    expect_r1_error_containing(
        "lr_while_cond_closure_capture",
        SRC_R1_STATE,
        &[WHILE_COND_REFUSAL, "`v`"],
    );
}

#[test]
fn liar_r1_while_cond_inner_if_write_is_refused() {
    expect_r1_error_containing(
        "lr_while_cond_inner_if_write",
        SRC_R1_STATE,
        &[WHILE_COND_REFUSAL, "`x`"],
    );
}

#[test]
fn liar_r1_while_cond_inner_block_write_is_refused() {
    expect_r1_error_containing(
        "lr_while_cond_inner_block_write",
        SRC_R1_STATE,
        &[WHILE_COND_REFUSAL, "`x`"],
    );
}

#[test]
fn liar_r1_while_cond_push_is_refused() {
    expect_r1_error_containing(
        "lr_while_cond_push",
        SRC_R1_STATE,
        &[WHILE_COND_REFUSAL, "`v`"],
    );
}

#[test]
fn liar_r1_while_cond_add_assign_then_arith_is_refused() {
    expect_r1_error_containing(
        "lr_while_cond_add_assign_then_arith",
        SRC_R1_STATE,
        &[WHILE_COND_REFUSAL, "`x`"],
    );
}

#[test]
fn liar_r1_while_cond_block_assign_local_is_refuted() {
    // The plain-assignment twin was already refuted at HEAD; it stays refuted.
    expect_r1_counterexample("lr_while_cond_block_assign_local", SRC_R1_STATE);
}

#[test]
fn control_r1_cmp_local_compound_true_verifies() {
    expect_r1_verified("cr_cmp_local_compound_true", SRC_R1_STATE);
}

#[test]
fn control_r1_idx_plain_verifies() {
    expect_r1_verified("cr_idx_plain", SRC_R1_STATE);
}

#[test]
fn control_r1_while_pure_cond_verifies() {
    expect_r1_verified("cr_while_pure_cond", SRC_R1_STATE);
}

#[test]
fn control_r1_while_len_cond_verifies() {
    expect_r1_verified("cr_while_len_cond", SRC_R1_STATE);
}

// ---- pre-existing: `push` / `vec!` arguments only rendered ----

const SRC_R1_ARGS: &str = r#"#![allow(unused)]
#![allow(arithmetic_overflow)]

// ---- `push` / `vec!` arguments were rendered, never visited ----

// LIAR: the nested assertion fails.
#[trust_vc::ensures(true)]
fn lr_push_nested_assert() {
    let mut w: Vec<u64> = Vec::new();
    w.push({
        assert!(false);
        5u64
    });
}

// LIAR: fails.
#[trust_vc::ensures(true)]
fn lr_vec_macro_nested_assert() {
    let _w: Vec<u64> = vec![{
        assert!(false);
        5u64
    }];
}

// LIAR: fails (k is 1).
#[trust_vc::ensures(true)]
fn lr_push_let_then_assert() {
    let mut w: Vec<u64> = Vec::new();
    w.push({
        let k: u64 = 1u64;
        assert!(k == 2u64);
        k
    });
}

// LIAR: fails.
#[trust_vc::ensures(true)]
fn lr_push_assert_eq() {
    let mut w: Vec<u64> = Vec::new();
    w.push({
        assert_eq!(1u64, 2u64);
        5u64
    });
}

// LIAR: fails at b = true.
#[trust_vc::requires(b)]
#[trust_vc::ensures(true)]
fn lr_push_if_assert(b: bool) {
    let mut w: Vec<u64> = Vec::new();
    w.push(if b {
        assert!(false);
        1u64
    } else {
        2u64
    });
}

// LIAR: fails on the first iteration.
#[trust_vc::ensures(true)]
fn lr_push_loop_assert() {
    let mut w: Vec<u64> = Vec::new();
    w.push({
        let mut i: u64 = 0u64;
        while i < 1u64 {
            assert!(i == 5u64);
            i = i + 1u64;
        }
        3u64
    });
}

// LIAR: overflows at n = 255.
#[trust_vc::requires(n == 255u8)]
#[trust_vc::ensures(true)]
fn lr_push_arith_overflow(n: u8) {
    let mut w: Vec<u8> = Vec::new();
    w.push({
        let k: u8 = n + 1u8;
        k
    });
}

// LIAR: overflows at n = 255 (`vec!` element).
#[trust_vc::requires(n == 255u8)]
#[trust_vc::ensures(true)]
fn lr_vec_elem_arith(n: u8) {
    let _w: Vec<u8> = vec![n + 1u8];
}

// LIAR: overflows at n = 255 (`vec!` block element).
#[trust_vc::requires(n == 255u8)]
#[trust_vc::ensures(true)]
fn lr_vec_elem_block_arith(n: u8) {
    let _w: Vec<u8> = vec![{
        let k: u8 = n + 1u8;
        k
    }];
}

// CONTROL: a plain push.
#[trust_vc::ensures(true)]
fn cr_push_plain() {
    let mut w: Vec<u64> = Vec::new();
    w.push(5u64);
    assert!(w.len() == 1usize);
}

// CONTROL: an in-range push argument.
#[trust_vc::requires(n < 255u8)]
#[trust_vc::ensures(true)]
fn cr_push_arith_ok(n: u8) {
    let mut w: Vec<u8> = Vec::new();
    w.push(n + 1u8);
}

// CONTROL: a plain `vec!`.
#[trust_vc::ensures(true)]
fn cr_vec_macro_plain() {
    let w: Vec<u64> = vec![1u64, 2u64];
    assert!(w.len() == 2usize);
}
"#;

#[test]
fn liar_r1_push_nested_assert_is_refuted() {
    expect_r1_counterexample_on("lr_push_nested_assert", SRC_R1_ARGS, "assertion");
}

#[test]
fn liar_r1_vec_macro_nested_assert_is_refuted() {
    expect_r1_counterexample_on("lr_vec_macro_nested_assert", SRC_R1_ARGS, "assertion");
}

#[test]
fn liar_r1_push_let_then_assert_is_refuted() {
    expect_r1_counterexample_on("lr_push_let_then_assert", SRC_R1_ARGS, "assertion");
}

#[test]
fn liar_r1_push_assert_eq_is_refuted() {
    expect_r1_counterexample_on("lr_push_assert_eq", SRC_R1_ARGS, "assertion");
}

#[test]
fn liar_r1_push_if_assert_is_refuted() {
    expect_r1_counterexample_on("lr_push_if_assert", SRC_R1_ARGS, "assertion");
}

#[test]
fn liar_r1_push_loop_assert_is_refuted() {
    expect_r1_counterexample_on("lr_push_loop_assert", SRC_R1_ARGS, "assertion");
}

#[test]
fn liar_r1_push_arith_overflow_is_refuted() {
    expect_r1_counterexample_on("lr_push_arith_overflow", SRC_R1_ARGS, "overflow_check");
}

#[test]
fn liar_r1_vec_elem_arith_is_refuted() {
    expect_r1_counterexample_on("lr_vec_elem_arith", SRC_R1_ARGS, "overflow_check");
}

#[test]
fn liar_r1_vec_elem_block_arith_is_refuted() {
    expect_r1_counterexample_on("lr_vec_elem_block_arith", SRC_R1_ARGS, "overflow_check");
}

#[test]
fn control_r1_push_plain_verifies() {
    expect_r1_verified("cr_push_plain", SRC_R1_ARGS);
}

#[test]
fn control_r1_push_arith_ok_verifies() {
    expect_r1_verified("cr_push_arith_ok", SRC_R1_ARGS);
}

#[test]
fn control_r1_vec_macro_plain_verifies() {
    expect_r1_verified("cr_vec_macro_plain", SRC_R1_ARGS);
}

// ---- pre-existing: by-value `self` of an impl for `&mut T` ----

const SRC_R1_REFMUT: &str = r#"#![allow(unused)]

struct S4 {
    a: u64,
}

// ---- by-value `self` of a trait implemented for `&mut T` ----
trait GrabRef {
    fn get(self, i: usize) -> u64;
}
impl<'a> GrabRef for &'a mut Vec<u64> {
    fn get(self, i: usize) -> u64 {
        self.push(7u64);
        i as u64
    }
}

trait CountRef {
    fn count(self) -> u64;
}
impl<'a> CountRef for &'a mut S4 {
    fn count(self) -> u64 {
        self.a = self.a + 1u64;
        0u64
    }
}

// LIAR: fails at b = true (v.len() is 1).
#[trust_vc::requires(b)]
#[trust_vc::ensures(true)]
fn lr_refmut_by_value_get(b: bool) {
    let mut v: Vec<u64> = Vec::new();
    if b {
        let _k = v.get(0usize);
    }
    assert!(v.len() == 0usize);
}

// LIAR: fails (k is 1).
#[trust_vc::ensures(true)]
fn lr_refmut_by_value_get_value_block() {
    let mut v: Vec<u64> = Vec::new();
    let k = {
        let _g = v.get(0usize);
        v.len()
    };
    assert!(k == 0usize);
}

// LIAR (refused): the push is invisible on a parameter too.
#[trust_vc::requires(v.len() == 0usize)]
#[trust_vc::ensures(true)]
fn lr_refmut_by_value_get_param(mut v: Vec<u64>) {
    let _k = v.get(0usize);
    assert!(v.len() == 0usize);
}

// LIAR: fails at b = true (s.a is 1).
#[trust_vc::requires(b)]
#[trust_vc::ensures(true)]
fn lr_refmut_by_value_count_local(b: bool) {
    let mut s = S4 { a: 0u64 };
    if b {
        let _k = s.count();
    }
    assert!(s.a == 0u64);
}

// LIAR: fails (s.a is 1).
#[trust_vc::requires(s.a == 0u64)]
#[trust_vc::ensures(true)]
fn lr_refmut_by_value_count_param(mut s: S4) {
    let _k = s.count();
    assert!(s.a == 0u64);
}

// CONTROL: a by-value impl for a SHARED reference is pure.
trait PureRef {
    fn peekv(self) -> u64;
}
impl PureRef for &S4 {
    fn peekv(self) -> u64 {
        self.a
    }
}

#[trust_vc::requires(s.a == 0u64)]
#[trust_vc::ensures(true)]
fn cr_shared_ref_by_value(s: S4) {
    let _k = s.peekv();
    assert!(s.a == 0u64);
}
"#;

#[test]
fn liar_r1_refmut_by_value_get_is_refused() {
    expect_r1_error_containing(
        "lr_refmut_by_value_get",
        SRC_R1_REFMUT,
        &[SHADOW_REFUSAL, "`.get(..)`", "mut Vec"],
    );
}

#[test]
fn liar_r1_refmut_by_value_get_value_block_is_refused() {
    expect_r1_error_containing(
        "lr_refmut_by_value_get_value_block",
        SRC_R1_REFMUT,
        &[SHADOW_REFUSAL, "`.get(..)`", "mut Vec"],
    );
}

#[test]
fn liar_r1_refmut_by_value_get_param_is_refused() {
    expect_r1_error_containing(
        "lr_refmut_by_value_get_param",
        SRC_R1_REFMUT,
        &[SHADOW_REFUSAL, "`.get(..)`", "mut Vec"],
    );
}

#[test]
fn liar_r1_refmut_by_value_count_local_fails_closed() {
    expect_r1_error_containing(
        "lr_refmut_by_value_count_local",
        SRC_R1_REFMUT,
        &[UNRESOLVED, "`s`"],
    );
}

#[test]
fn liar_r1_refmut_by_value_count_param_fails_closed() {
    // The registry classifies `count` as a by-value `&mut` receiver
    // (`SelfReceiverKind::ValueMutRef`); review round 2 moved that kind from
    // the struct havoc (which refuted runtime-TRUE sibling-field claims) to a
    // poison, so the stale claim is a fail-closed error rather than a model.
    expect_r1_error_containing(
        "lr_refmut_by_value_count_param",
        SRC_R1_REFMUT,
        &[UNRESOLVED, "`s`"],
    );
}

#[test]
fn control_r1_shared_ref_by_value_verifies() {
    expect_r1_verified("cr_shared_ref_by_value", SRC_R1_REFMUT);
}

// ---- pre-existing: an impl declared by an item macro ----

const SRC_R1_MACRO: &str = r#"#![allow(unused)]

macro_rules! mk_shadow {
    () => {
        trait Firsty {
            fn first(&mut self) -> u64;
        }
        impl Firsty for Vec<u64> {
            fn first(&mut self) -> u64 {
                self.push(1u64);
                0u64
            }
        }
    };
}
mk_shadow!();

// LIAR: fails at b = true (the macro-declared `first(&mut self)` pushes).
#[trust_vc::requires(b)]
#[trust_vc::ensures(true)]
fn lr_macro_generated_shadow(b: bool) {
    let mut v: Vec<u64> = Vec::new();
    if b {
        let _k = v.first();
    }
    assert!(v.len() == 0usize);
}

// TRUE, but refused: `mk_shadow!` emits an impl and a trait this lane does not
// read, which can change what any function of the file does.
#[trust_vc::ensures(true)]
fn cr_macro_shadow_neighbour() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    assert!(v.len() == 1usize);
}
"#;

/// A macro that declares nothing hazardous, in a file of its own.
const SRC_R1_PLAIN_MACRO: &str = r#"#![allow(unused)]

// CONTROL: a macro that declares nothing hazardous.
macro_rules! mk_plain {
    () => {
        fn helper_plain(n: u64) -> u64 {
            n
        }
    };
}
mk_plain!();

#[trust_vc::ensures(true)]
fn cr_plain_macro_neighbour() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1u64);
    assert!(v.len() == 1usize);
}
"#;

#[test]
fn liar_r1_macro_generated_shadow_is_refused() {
    expect_r1_error_containing(
        "lr_macro_generated_shadow",
        SRC_R1_MACRO,
        &[SHADOW_REFUSAL, "`.first(..)`", MACRO_SHADOW_ORIGIN],
    );
}

#[test]
fn control_r1_plain_macro_neighbour_verifies() {
    expect_r1_verified("cr_plain_macro_neighbour", SRC_R1_PLAIN_MACRO);
}

#[test]
fn a_neighbour_of_a_macro_that_emits_an_impl_is_refused() {
    expect_r1_error_containing(
        "cr_macro_shadow_neighbour",
        SRC_R1_MACRO,
        &["unread item", "`mk_shadow!`"],
    );
}

// ---- pre-existing: a shadowed pure method inside an `assert!` argument ----

const SRC_R1_ASSERTARG: &str = r#"#![allow(unused)]

trait Look {
    fn contains(&mut self, k: u64) -> bool;
}
impl Look for Vec<u64> {
    fn contains(&mut self, k: u64) -> bool {
        self.push(k);
        false
    }
}

// LIAR: the first assert RUNS the user's `contains(&mut self)`; the second fails.
#[trust_vc::ensures(true)]
fn lr_shadow_in_assert_arg() {
    let mut v: Vec<u64> = Vec::new();
    assert!(!v.contains(1u64));
    assert!(v.len() == 0usize);
}

// LIAR: same through the `trust_vc::assert!` spelling.
#[trust_vc::ensures(true)]
fn lr_shadow_in_trust_vc_assert_arg() {
    let mut v: Vec<u64> = Vec::new();
    trust_vc::assert!(!v.contains(1u64));
    assert!(v.len() == 0usize);
}

// LIAR (already refused since rank 4): the `if`-condition position.
#[trust_vc::ensures(true)]
fn lr_shadow_in_if_cond() {
    let mut v: Vec<u64> = Vec::new();
    if v.contains(1u64) {}
    assert!(v.len() == 0usize);
}
"#;

#[test]
fn liar_r1_shadow_in_assert_arg_is_refused() {
    expect_r1_error_containing(
        "lr_shadow_in_assert_arg",
        SRC_R1_ASSERTARG,
        &[SHADOW_REFUSAL, "`.contains(..)`"],
    );
}

#[test]
fn liar_r1_shadow_in_trust_vc_assert_arg_is_refused() {
    expect_r1_error_containing(
        "lr_shadow_in_trust_vc_assert_arg",
        SRC_R1_ASSERTARG,
        &[SHADOW_REFUSAL, "`.contains(..)`"],
    );
}

#[test]
fn liar_r1_shadow_in_if_cond_is_refused() {
    expect_r1_error_containing(
        "lr_shadow_in_if_cond",
        SRC_R1_ASSERTARG,
        &[SHADOW_REFUSAL, "`.contains(..)`"],
    );
}

// ---- pre-existing: the raw-identifier `#[r#cfg]` spelling ----

const SRC_R1_RAWCFG: &str = r#"#![allow(unused)]

#[r#cfg(any())]
const K: u64 = 1u64;
#[r#cfg(not(any()))]
const K: u64 = 2u64;

// LIAR: rustc removes the gated `if`, so x stays 0 and the assert fails at b = true.
#[trust_vc::requires(b)]
#[trust_vc::ensures(true)]
fn lr_raw_cfg_if(b: bool) {
    let mut x: u64 = 0u64;
    #[r#cfg(any())]
    if b {
        x = 5u64;
    }
    assert!(x == 5u64 || !b);
}

// LIAR: the gated shadow is removed; x stays 1.
#[trust_vc::ensures(true)]
fn lr_raw_cfg_let_shadow() {
    let x: u64 = 1u64;
    #[r#cfg(any())]
    let x: u64 = 2u64;
    assert!(x == 2u64);
}

// LIAR: the live `K` is 2.
#[trust_vc::ensures(result == 1u64)]
fn lr_raw_cfg_const() -> u64 {
    K
}

// LIAR: `r#cfg_attr` expands to a `cfg(any())` that removes the `if`.
#[trust_vc::requires(b)]
#[trust_vc::ensures(true)]
fn lr_raw_cfg_attr_inner(b: bool) {
    let mut x: u64 = 0u64;
    #[r#cfg_attr(not(any()), cfg(any()))]
    if b {
        x = 5u64;
    }
    assert!(x == 5u64 || !b);
}

// LIAR (already refused since rank 6): the plain spelling.
#[trust_vc::requires(b)]
#[trust_vc::ensures(true)]
fn lr_plain_cfg_if(b: bool) {
    let mut x: u64 = 0u64;
    #[cfg(any())]
    if b {
        x = 5u64;
    }
    assert!(x == 5u64 || !b);
}
"#;

#[test]
fn liar_r1_raw_cfg_if_is_refused() {
    expect_c6_body_cfg_refused("lr_raw_cfg_if", SRC_R1_RAWCFG);
}

#[test]
fn liar_r1_raw_cfg_let_shadow_is_refused() {
    expect_c6_body_cfg_refused("lr_raw_cfg_let_shadow", SRC_R1_RAWCFG);
}

#[test]
fn liar_r1_raw_cfg_attr_inner_is_refused() {
    expect_c6_body_cfg_refused("lr_raw_cfg_attr_inner", SRC_R1_RAWCFG);
}

#[test]
fn liar_r1_plain_cfg_if_is_refused() {
    expect_c6_body_cfg_refused("lr_plain_cfg_if", SRC_R1_RAWCFG);
}

#[test]
fn liar_r1_raw_cfg_const_is_refused() {
    expect_c6_file_cfg_refused("lr_raw_cfg_const", SRC_R1_RAWCFG, "K");
}

// ============================================================================
// Review round 2 — regressions of review round 1 (2026-09-15)
// ============================================================================

const LOOP_RECEIVER_REFUSAL: &str =
    "inside a loop body may change it, and the loop frame does not havoc a method receiver";
const MUT_STRUCT_POSTCONDITION_REJECT: &str =
    "which is mutated in place by a `&mut self` (or unresolved) method";

// ---- round-1 regression: `vec!` elements and block / value-`if` / `match`
// mutator arguments emitted loop-body sites over the loop havoc symbols ----

const SRC_R2_SITES: &str = r#"#![allow(unused)]

// GATED (runtime-true, HEAD Verified, round 1 REFUTED it over `x__loopbody_N`):
// a `vec!` element over a loop-modified operand.
#[trust_vc::ensures(true)]
fn gr2_vec_elem_loop_modified() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<u8> = vec![x + 1u8];
        x = 1u8;
        i += 1u8;
    }
}

// GATED: the repeat-element form.
#[trust_vc::ensures(true)]
fn gr2_vec_repeat_elem_loop_modified() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<u8> = vec![x + 1u8; 2];
        x = 1u8;
        i += 1u8;
    }
}

// GATED: the repeat-LENGTH form.
#[trust_vc::ensures(true)]
fn gr2_vec_repeat_len_loop_modified() {
    let mut x: usize = 0usize;
    let mut i: usize = 0usize;
    while i < 10usize {
        let w: Vec<u8> = vec![0u8; x + 1usize];
        x = 1usize;
        i += 1usize;
    }
}

// GATED: the element under a branch inside the loop.
#[trust_vc::ensures(true)]
fn gr2_vec_branch_loop_modified() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        if i > 0u8 {
            let w: Vec<u8> = vec![x + 1u8];
        }
        x = 1u8;
        i += 1u8;
    }
}

// GATED: a nested `vec!`.
#[trust_vc::ensures(true)]
fn gr2_vec_nested_loop_modified() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<Vec<u8>> = vec![vec![x + 1u8]];
        x = 1u8;
        i += 1u8;
    }
}

// GATED: the operand is reset from a requires-bounded parameter.
#[trust_vc::requires(n < 100u8)]
#[trust_vc::ensures(true)]
fn gr2_vec_loop_modified_from_param(n: u8) {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<u8> = vec![x + 1u8];
        x = n;
        i += 1u8;
    }
}

// GATED: a block element.
#[trust_vc::ensures(true)]
fn gr2_vec_block_elem_loop_modified() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<u8> = vec![{ x + 1u8 }];
        x = 1u8;
        i += 1u8;
    }
}

// GATED: `vec!` as a mutator argument.
#[trust_vc::ensures(true)]
fn gr2_extend_vec_loop_modified() {
    let mut v: Vec<u8> = Vec::new();
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.extend(vec![x + 1u8]);
        x = 1u8;
        i += 1u8;
    }
}

// GATED: a block mutator argument.
#[trust_vc::ensures(true)]
fn gr2_push_block_loop_modified() {
    let mut v: Vec<u8> = Vec::new();
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push({ x + 1u8 });
        x = 1u8;
        i += 1u8;
    }
}

// GATED: a block mutator argument with a `let`.
#[trust_vc::ensures(true)]
fn gr2_push_block_let_loop_modified() {
    let mut v: Vec<u8> = Vec::new();
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push({
            let k: u8 = x + 1u8;
            k
        });
        x = 1u8;
        i += 1u8;
    }
}

// GATED: a value-`if` mutator argument.
#[trust_vc::ensures(true)]
fn gr2_push_if_value_loop_modified(b: bool) {
    let mut v: Vec<u8> = Vec::new();
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push(if b { x + 1u8 } else { 0u8 });
        x = 1u8;
        i += 1u8;
    }
}

// GATED: a `match` mutator argument.
#[trust_vc::ensures(true)]
fn gr2_push_match_value_loop_modified(b: bool) {
    let mut v: Vec<u8> = Vec::new();
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push(match b {
            true => x + 1u8,
            false => 0u8,
        });
        x = 1u8;
        i += 1u8;
    }
}

// GATED (the refusal is name-based, so a guard-bounded operand fails closed
// too, exactly like the rank-1 `s.f = i + 1u8` control): the guard var.
#[trust_vc::ensures(true)]
fn gr2_vec_guard_bounded() {
    let mut x: u8 = 0u8;
    while x < 10u8 {
        let w: Vec<u8> = vec![x + 1u8];
        x += 1u8;
    }
}

// GATED: the `for` var.
#[trust_vc::ensures(true)]
fn gr2_vec_for_var() {
    for i in 0u8..10u8 {
        let w: Vec<u8> = vec![i + 1u8];
    }
}

// GATED: a block mutator argument over the guard var.
#[trust_vc::ensures(true)]
fn gr2_push_block_guard_bounded() {
    let mut v: Vec<u8> = Vec::new();
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push({ i + 1u8 });
        i += 1u8;
    }
}

// GATED: an invariant written first does not lift the refusal.
#[trust_vc::ensures(true)]
fn gr2_vec_invariant_first() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        invariant!(x <= 1u8);
        let w: Vec<u8> = vec![x + 1u8];
        x = 1u8;
        i += 1u8;
    }
}

// GATED: the repeat length over the guard var.
#[trust_vc::ensures(true)]
fn gr2_vec_repeat_len_guard_bounded() {
    let mut i: usize = 0usize;
    while i < 10usize {
        let w: Vec<u8> = vec![0u8; i + 1usize];
        i += 1usize;
    }
}

// GATED (HEAD refuted this true loop through the block's own statement lane;
// the rank-1 scrutinee refusal now collects the block's site too): an `if
// let` scrutinee that is a block over a loop-modified operand.
#[trust_vc::ensures(true)]
fn gr2_if_let_block_scrutinee_loop_modified() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        if let 0u8 = { x + 1u8 } {}
        x = 1u8;
        i += 1u8;
    }
}

// LIAR (refused): the same `vec!` element over an operand that overflows on
// the second iteration.
#[trust_vc::ensures(true)]
fn lr2_vec_elem_overflow() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<u8> = vec![x + 1u8];
        x = 255u8;
        i += 1u8;
    }
}

// LIAR (refused): the repeat length overflows on the second iteration.
#[trust_vc::ensures(true)]
fn lr2_vec_repeat_len_overflow() {
    let mut x: usize = 0usize;
    let mut i: usize = 0usize;
    while i < 2usize {
        let w: Vec<u8> = vec![0u8; x + 1usize];
        x = usize::MAX;
        i += 1usize;
    }
}

// LIAR (refused): a block mutator argument that overflows.
#[trust_vc::ensures(true)]
fn lr2_push_block_overflow() {
    let mut v: Vec<u8> = Vec::new();
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push({ x + 1u8 });
        x = 255u8;
        i += 1u8;
    }
}

// LIAR (refused): a value-`if` mutator argument that overflows at b = true.
#[trust_vc::ensures(true)]
fn lr2_push_if_value_overflow(b: bool) {
    let mut v: Vec<u8> = Vec::new();
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push(if b { x + 1u8 } else { 0u8 });
        x = 255u8;
        i += 1u8;
    }
}

// LIAR (refuted; the round-1 straight-line site stays live): a `vec!`
// element overflow outside any loop.
#[trust_vc::requires(x == 255u8)]
#[trust_vc::ensures(true)]
fn lr2_vec_elem_straight_overflow(x: u8) {
    let w: Vec<u8> = vec![x + 1u8];
}

// LIAR (refuted): a block mutator argument overflow outside any loop.
#[trust_vc::requires(x == 255u8)]
#[trust_vc::ensures(true)]
fn lr2_push_block_straight_overflow(x: u8) {
    let mut v: Vec<u8> = Vec::new();
    v.push({ x + 1u8 });
}

// LIAR (refuted): a value-`if` mutator argument overflow outside any loop.
#[trust_vc::requires(x == 255u8 && b)]
#[trust_vc::ensures(true)]
fn lr2_push_if_value_straight_overflow(x: u8, b: bool) {
    let mut v: Vec<u8> = Vec::new();
    v.push(if b { x + 1u8 } else { 0u8 });
}

// LIAR (refuted): a spec assertion nested in a mutator-argument block.
#[trust_vc::ensures(true)]
fn lr2_push_block_nested_assert() {
    let mut v: Vec<u64> = Vec::new();
    v.push({
        assert!(false);
        5u64
    });
}

// LIAR (refuted): a block mutator argument over a loop-INVARIANT parameter
// operand is rendered exactly and emitted (n = 255 overflows).
#[trust_vc::ensures(true)]
fn lr2_push_block_param_operand(n: u8) {
    let mut v: Vec<u8> = Vec::new();
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push({ n + 1u8 });
        i += 1u8;
    }
}

// LIAR (refuted): a `vec!` element over a loop-invariant parameter operand.
#[trust_vc::ensures(true)]
fn lr2_vec_elem_param_operand(n: u8) {
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<u8> = vec![n + 1u8];
        i += 1u8;
    }
}

// CONTROL: the same two sites under a bounding requires verify.
#[trust_vc::requires(n < 200u8)]
#[trust_vc::ensures(true)]
fn cr2_push_block_param_operand(n: u8) {
    let mut v: Vec<u8> = Vec::new();
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push({ n + 1u8 });
        i += 1u8;
    }
}

#[trust_vc::requires(n < 200u8)]
#[trust_vc::ensures(true)]
fn cr2_vec_elem_param_operand(n: u8) {
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<u8> = vec![n + 1u8];
        i += 1u8;
    }
}

// CONTROL: no arithmetic site at all is never refused.
#[trust_vc::ensures(true)]
fn cr2_push_block_no_arith() {
    let mut v: Vec<u8> = Vec::new();
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push({ x });
        x = 1u8;
        i += 1u8;
    }
}

#[trust_vc::ensures(true)]
fn cr2_vec_elem_no_arith() {
    let mut x: u8 = 0u8;
    let mut i: u8 = 0u8;
    while i < 10u8 {
        let w: Vec<u8> = vec![x];
        x = 1u8;
        i += 1u8;
    }
}

// CONTROL: an index read is not an arithmetic site (index bounds are never
// emitted inside a loop body, so it is not scanned either).
#[trust_vc::ensures(true)]
fn cr2_vec_elem_index_loop() {
    let a: [u8; 3] = [1u8, 2u8, 3u8];
    let mut i: usize = 0usize;
    while i < 3usize {
        let w: Vec<u8> = vec![a[i]];
        i += 1usize;
    }
}

// CONTROL: a PLAIN mutator argument over the guard var is the enclosing
// statement's own site (HEAD behaviour, untouched).
#[trust_vc::ensures(true)]
fn cr2_push_plain_guard_bounded() {
    let mut v: Vec<u8> = Vec::new();
    let mut i: u8 = 0u8;
    while i < 10u8 {
        v.push(i + 1u8);
        i += 1u8;
    }
}

// CONTROL: the straight-line forms verify under a bounding requires.
#[trust_vc::requires(x < 255u8)]
#[trust_vc::ensures(true)]
fn cr2_vec_elem_straight(x: u8) {
    let w: Vec<u8> = vec![x + 1u8];
}

#[trust_vc::requires(x < 255u8)]
#[trust_vc::ensures(true)]
fn cr2_push_block_straight(x: u8) {
    let mut v: Vec<u8> = Vec::new();
    v.push({ x + 1u8 });
}

#[trust_vc::requires(n < 10usize)]
#[trust_vc::ensures(true)]
fn cr2_vec_repeat_len_straight(n: usize) {
    let w: Vec<u8> = vec![0u8; n + 1usize];
}
"#;

#[test]
fn gated_r2_vec_elem_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_elem_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_repeat_elem_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_repeat_elem_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_repeat_len_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_repeat_len_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1usize`",
        ],
    );
}

#[test]
fn gated_r2_vec_branch_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_branch_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_nested_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_nested_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_loop_modified_from_param_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_loop_modified_from_param",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_block_elem_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_block_elem_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_extend_vec_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_extend_vec_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_push_block_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_push_block_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an argument of a collection-mutator call",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_push_block_let_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_push_block_let_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an argument of a collection-mutator call",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_push_if_value_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_push_if_value_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an argument of a collection-mutator call",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_push_match_value_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_push_match_value_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an argument of a collection-mutator call",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_guard_bounded_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_guard_bounded",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_for_var_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_for_var",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`i + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_push_block_guard_bounded_fails_closed() {
    expect_r1_error_containing(
        "gr2_push_block_guard_bounded",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an argument of a collection-mutator call",
            "`i + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_invariant_first_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_invariant_first",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn gated_r2_vec_repeat_len_guard_bounded_fails_closed() {
    expect_r1_error_containing(
        "gr2_vec_repeat_len_guard_bounded",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an element of an exec `vec!`",
            "`i + 1usize`",
        ],
    );
}

#[test]
fn gated_r2_if_let_block_scrutinee_loop_modified_fails_closed() {
    expect_r1_error_containing(
        "gr2_if_let_block_scrutinee_loop_modified",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "the scrutinee of an `if let`",
            "`x + 1u8`",
        ],
    );
}

#[test]
fn liar_r2_vec_elem_overflow_is_refused() {
    expect_r1_error_containing(
        "lr2_vec_elem_overflow",
        SRC_R2_SITES,
        &[LOOP_HAVOC_SITE_REFUSAL, "an element of an exec `vec!`"],
    );
}

#[test]
fn liar_r2_vec_repeat_len_overflow_is_refused() {
    expect_r1_error_containing(
        "lr2_vec_repeat_len_overflow",
        SRC_R2_SITES,
        &[LOOP_HAVOC_SITE_REFUSAL, "an element of an exec `vec!`"],
    );
}

#[test]
fn liar_r2_push_block_overflow_is_refused() {
    expect_r1_error_containing(
        "lr2_push_block_overflow",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an argument of a collection-mutator call",
        ],
    );
}

#[test]
fn liar_r2_push_if_value_overflow_is_refused() {
    expect_r1_error_containing(
        "lr2_push_if_value_overflow",
        SRC_R2_SITES,
        &[
            LOOP_HAVOC_SITE_REFUSAL,
            "an argument of a collection-mutator call",
        ],
    );
}

#[test]
fn liar_r2_vec_elem_straight_overflow_is_refuted() {
    expect_r1_counterexample_on("lr2_vec_elem_straight_overflow", SRC_R2_SITES, "overflow");
}

#[test]
fn liar_r2_push_block_straight_overflow_is_refuted() {
    expect_r1_counterexample_on("lr2_push_block_straight_overflow", SRC_R2_SITES, "overflow");
}

#[test]
fn liar_r2_push_if_value_straight_overflow_is_refuted() {
    expect_r1_counterexample_on(
        "lr2_push_if_value_straight_overflow",
        SRC_R2_SITES,
        "overflow",
    );
}

#[test]
fn liar_r2_push_block_nested_assert_is_refuted() {
    expect_r1_counterexample_on("lr2_push_block_nested_assert", SRC_R2_SITES, "assertion");
}

#[test]
fn liar_r2_push_block_param_operand_is_refuted() {
    expect_r1_counterexample_on("lr2_push_block_param_operand", SRC_R2_SITES, "overflow");
}

#[test]
fn liar_r2_vec_elem_param_operand_is_refuted() {
    expect_r1_counterexample_on("lr2_vec_elem_param_operand", SRC_R2_SITES, "overflow");
}

#[test]
fn control_r2_push_block_param_operand_verifies() {
    expect_r1_verified("cr2_push_block_param_operand", SRC_R2_SITES);
}

#[test]
fn control_r2_vec_elem_param_operand_verifies() {
    expect_r1_verified("cr2_vec_elem_param_operand", SRC_R2_SITES);
}

#[test]
fn control_r2_push_block_no_arith_verifies() {
    expect_r1_verified("cr2_push_block_no_arith", SRC_R2_SITES);
}

#[test]
fn control_r2_vec_elem_no_arith_verifies() {
    expect_r1_verified("cr2_vec_elem_no_arith", SRC_R2_SITES);
}

#[test]
fn control_r2_vec_elem_index_loop_verifies() {
    expect_r1_verified("cr2_vec_elem_index_loop", SRC_R2_SITES);
}

#[test]
fn control_r2_push_plain_guard_bounded_verifies() {
    expect_r1_verified("cr2_push_plain_guard_bounded", SRC_R2_SITES);
}

#[test]
fn control_r2_vec_elem_straight_verifies() {
    expect_r1_verified("cr2_vec_elem_straight", SRC_R2_SITES);
}

#[test]
fn control_r2_push_block_straight_verifies() {
    expect_r1_verified("cr2_push_block_straight", SRC_R2_SITES);
}

#[test]
fn control_r2_vec_repeat_len_straight_verifies() {
    expect_r1_verified("cr2_vec_repeat_len_straight", SRC_R2_SITES);
}

// ---- round-1 regression: by-value `self` of an `impl .. for &mut T` was
// registered as `&mut self` and HAVOCKED the receiver ----

const SRC_R2_VALMUTREF: &str = r#"#![allow(unused)]

struct S4 {
    a: u64,
    b: u64,
}
enum E4 {
    A(u64),
    B,
}
struct W4 {
    s: S4,
}
struct H4 {
    s: S4,
    n: u64,
}
impl S4 {
    fn get_a(&self) -> u64 {
        self.a
    }
}
trait PeekRef {
    fn peek(self) -> u64;
}
impl<'a> PeekRef for &'a mut S4 {
    fn peek(self) -> u64 {
        self.a
    }
}
impl<'a> PeekRef for &'a mut E4 {
    fn peek(self) -> u64 {
        0u64
    }
}
trait TouchB {
    fn touch_b(self) -> u64;
}
impl<'a> TouchB for &'a mut S4 {
    fn touch_b(self) -> u64 {
        self.b = self.b + 1u64;
        self.b
    }
}
trait PureRef {
    fn peekv(self) -> u64;
}
impl PureRef for &S4 {
    fn peekv(self) -> u64 {
        self.a
    }
}

// GATED (runtime-true, HEAD Verified, round 1 REFUTED it through the struct
// havoc): a read-only by-value `&mut S4` method, then a claim on a field.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_param(mut s: S4) {
    let _k = s.peek();
    assert!(s.a == 5u64);
}

// GATED: the method writes the OTHER field.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_touch_b_sibling_field(mut s: S4) {
    let _k = s.touch_b();
    assert!(s.a == 5u64);
}

// GATED: the call in a branch (the join re-poisons the receiver).
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_branch(mut s: S4, b: bool) {
    if b {
        let _k = s.peek();
    }
    assert!(s.a == 5u64);
}

// GATED: in a `match` arm.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_match(mut s: S4, b: bool) {
    match b {
        true => {
            let _k = s.peek();
        }
        false => {}
    }
    assert!(s.a == 5u64);
}

// GATED: in a block.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_block(mut s: S4) {
    {
        let _k = s.peek();
    }
    assert!(s.a == 5u64);
}

// GATED (the loop is refused: the receiver is poisoned, not framed).
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_while_loop(mut s: S4) {
    let mut i: u8 = 0u8;
    while i < 3u8 {
        let _k = s.peek();
        i += 1u8;
    }
    assert!(s.a == 5u64);
}

#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_for_loop(mut s: S4) {
    for i in 0u8..3u8 {
        let _k = s.peek();
    }
    assert!(s.a == 5u64);
}

#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_bare_loop(mut s: S4) {
    loop {
        let _k = s.peek();
        break;
    }
    assert!(s.a == 5u64);
}

#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_while_invariant(mut s: S4) {
    let mut i: u8 = 0u8;
    while i < 3u8 {
        invariant!(s.a == 5u64);
        let _k = s.peek();
        i += 1u8;
    }
    assert!(s.a == 5u64);
}

// GATED: an enum receiver.
#[trust_vc::requires(matches!(e, E4::B))]
#[trust_vc::ensures(true)]
fn gr2_enum_peek_param(mut e: E4) {
    let _k = e.peek();
    match e {
        E4::A(_) => assert!(false),
        E4::B => {}
    }
}

// GATED: a nested-field receiver (the root is poisoned).
#[trust_vc::requires(w.s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_nested_field_peek_param(mut w: W4) {
    let _k = w.s.peek();
    assert!(w.s.a == 5u64);
}

// GATED: a holder's sibling field.
#[trust_vc::requires(h.n == 7u64)]
#[trust_vc::ensures(true)]
fn gr2_holder_field_peek_sibling(mut h: H4) {
    let _k = h.s.peek();
    assert!(h.n == 7u64);
}

// GATED: the returned sibling field (the return lane reads the poison).
#[trust_vc::requires(s.a == 5u64 && s.b == 3u64)]
#[trust_vc::ensures(result == 3u64)]
fn gr2_peek_then_return_sibling(mut s: S4) -> u64 {
    let _k = s.peek();
    s.b
}

// GATED: through a `&mut S4` parameter.
#[trust_vc::requires(r.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_through_ref_param(r: &mut S4) {
    let _k = r.peek();
    assert!(r.a == 5u64);
}

// GATED: a `&mut S4` parameter's postcondition (the two-state reject).
#[trust_vc::requires(r.a == 5u64)]
#[trust_vc::ensures(r.a == 5u64)]
fn gr2_peek_ref_param_ensures(r: &mut S4) {
    let _k = r.peek();
}

// GATED: a pure getter after the call reads the poison.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_then_getter(mut s: S4) {
    let _k = s.peek();
    assert!(s.get_a() == 5u64);
}

// GATED: the UFCS spelling.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn gr2_peek_ufcs(mut s: S4) {
    let _k = PeekRef::peek(&mut s);
    assert!(s.a == 5u64);
}

// LIAR (fails closed): the write to `b` is real (s.b is 1).
#[trust_vc::requires(s.b == 0u64)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_stale(mut s: S4) {
    let _k = s.touch_b();
    assert!(s.b == 0u64);
}

// LIAR: in a branch, at b = true.
#[trust_vc::requires(s.b == 0u64 && b)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_branch(mut s: S4, b: bool) {
    if b {
        let _k = s.touch_b();
    }
    assert!(s.b == 0u64);
}

// LIAR: in a `match` arm, at b = true.
#[trust_vc::requires(s.b == 0u64 && b)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_match(mut s: S4, b: bool) {
    match b {
        true => {
            let _k = s.touch_b();
        }
        false => {}
    }
    assert!(s.b == 0u64);
}

// LIAR: in a block.
#[trust_vc::requires(s.b == 0u64)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_block(mut s: S4) {
    {
        let _k = s.touch_b();
    }
    assert!(s.b == 0u64);
}

// LIAR (refused): in a `while` loop (s.b is 3).
#[trust_vc::requires(s.b == 0u64)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_while(mut s: S4) {
    let mut i: u8 = 0u8;
    while i < 3u8 {
        let _k = s.touch_b();
        i += 1u8;
    }
    assert!(s.b == 0u64);
}

// LIAR (refused): in a `for` loop.
#[trust_vc::requires(s.b == 0u64)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_for(mut s: S4) {
    for i in 0u8..3u8 {
        let _k = s.touch_b();
    }
    assert!(s.b == 0u64);
}

// LIAR (refused): in a bare loop.
#[trust_vc::requires(s.b == 0u64)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_loop(mut s: S4) {
    loop {
        let _k = s.touch_b();
        break;
    }
    assert!(s.b == 0u64);
}

// LIAR (refused): a false invariant on the written field.
#[trust_vc::requires(s.b == 0u64)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_while_invariant(mut s: S4) {
    let mut i: u8 = 0u8;
    while i < 3u8 {
        invariant!(s.b == 0u64);
        let _k = s.touch_b();
        i += 1u8;
    }
    assert!(s.b == 0u64);
}

// LIAR (rejected postcondition): through a `&mut S4` parameter.
#[trust_vc::requires(r.b == 0u64)]
#[trust_vc::ensures(r.b == 0u64)]
fn lr2_touch_b_ref_param_ensures(r: &mut S4) {
    let _k = r.touch_b();
}

// LIAR: a nested-field receiver.
#[trust_vc::requires(w.s.b == 0u64)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_nested(mut w: W4) {
    let _k = w.s.touch_b();
    assert!(w.s.b == 0u64);
}

// LIAR: the UFCS spelling.
#[trust_vc::requires(s.b == 0u64)]
#[trust_vc::ensures(true)]
fn lr2_touch_b_ufcs(mut s: S4) {
    let _k = TouchB::touch_b(&mut s);
    assert!(s.b == 0u64);
}

// LIAR: the returned written field (result is 1).
#[trust_vc::requires(s.b == 0u64)]
#[trust_vc::ensures(result == 0u64)]
fn lr2_touch_b_return_field(mut s: S4) -> u64 {
    let _k = s.touch_b();
    s.b
}

// CONTROL: a `&self` getter declared beside the by-value impl is still pure.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn cr2_getter_beside_impl(s: S4) {
    let _k = s.get_a();
    assert!(s.a == 5u64);
}

// CONTROL: a by-value impl for a SHARED reference is pure.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(true)]
fn cr2_shared_ref_by_value(s: S4) {
    let _k = s.peekv();
    assert!(s.a == 5u64);
}

// CONTROL: a loop-local receiver nothing outside the loop reads.
#[trust_vc::ensures(true)]
fn cr2_peek_loop_local() {
    let mut i: u8 = 0u8;
    while i < 3u8 {
        let mut s = S4 { a: 5u64, b: 0u64 };
        let _k = s.peek();
        i += 1u8;
    }
}

// CONTROL (HEAD behaviour, untouched): a by-value parameter's postcondition
// reads its entry value.
#[trust_vc::requires(s.a == 5u64)]
#[trust_vc::ensures(s.a == 5u64)]
fn cr2_peek_ensures_by_value_param(mut s: S4) {
    let _k = s.peek();
}
"#;

#[test]
fn gated_r2_peek_param_fails_closed() {
    expect_r1_error_containing("gr2_peek_param", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn gated_r2_touch_b_sibling_field_fails_closed() {
    expect_r1_error_containing(
        "gr2_touch_b_sibling_field",
        SRC_R2_VALMUTREF,
        &[UNRESOLVED, "`s`"],
    );
}

#[test]
fn gated_r2_peek_branch_fails_closed() {
    expect_r1_error_containing("gr2_peek_branch", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn gated_r2_peek_match_fails_closed() {
    expect_r1_error_containing("gr2_peek_match", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn gated_r2_peek_block_fails_closed() {
    expect_r1_error_containing("gr2_peek_block", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn gated_r2_peek_while_loop_fails_closed() {
    expect_r1_error_containing(
        "gr2_peek_while_loop",
        SRC_R2_VALMUTREF,
        &[LOOP_RECEIVER_REFUSAL, "`s`"],
    );
}

#[test]
fn gated_r2_peek_for_loop_fails_closed() {
    expect_r1_error_containing(
        "gr2_peek_for_loop",
        SRC_R2_VALMUTREF,
        &[LOOP_RECEIVER_REFUSAL, "`s`"],
    );
}

#[test]
fn gated_r2_peek_bare_loop_fails_closed() {
    expect_r1_error_containing(
        "gr2_peek_bare_loop",
        SRC_R2_VALMUTREF,
        &[LOOP_RECEIVER_REFUSAL, "`s`"],
    );
}

#[test]
fn gated_r2_peek_while_invariant_fails_closed() {
    expect_r1_error_containing(
        "gr2_peek_while_invariant",
        SRC_R2_VALMUTREF,
        &[LOOP_RECEIVER_REFUSAL, "`s`"],
    );
}

#[test]
fn gated_r2_enum_peek_param_fails_closed() {
    expect_r1_error_containing(
        "gr2_enum_peek_param",
        SRC_R2_VALMUTREF,
        &[UNRESOLVED, "`e`"],
    );
}

#[test]
fn gated_r2_nested_field_peek_param_fails_closed() {
    expect_r1_error_containing(
        "gr2_nested_field_peek_param",
        SRC_R2_VALMUTREF,
        &[UNRESOLVED, "`w`"],
    );
}

#[test]
fn gated_r2_holder_field_peek_sibling_fails_closed() {
    expect_r1_error_containing(
        "gr2_holder_field_peek_sibling",
        SRC_R2_VALMUTREF,
        &[UNRESOLVED, "`h`"],
    );
}

#[test]
fn gated_r2_peek_then_return_sibling_fails_closed() {
    expect_r1_error_containing(
        "gr2_peek_then_return_sibling",
        SRC_R2_VALMUTREF,
        &[UNRESOLVED, "`s`"],
    );
}

#[test]
fn gated_r2_peek_through_ref_param_fails_closed() {
    expect_r1_error_containing(
        "gr2_peek_through_ref_param",
        SRC_R2_VALMUTREF,
        &[UNRESOLVED, "`r`"],
    );
}

#[test]
fn gated_r2_peek_ref_param_ensures_fails_closed() {
    expect_r1_error_containing(
        "gr2_peek_ref_param_ensures",
        SRC_R2_VALMUTREF,
        &[MUT_STRUCT_POSTCONDITION_REJECT, "`r`"],
    );
}

#[test]
fn gated_r2_peek_then_getter_fails_closed() {
    expect_r1_error_containing(
        "gr2_peek_then_getter",
        SRC_R2_VALMUTREF,
        &[UNRESOLVED, "`s`"],
    );
}

#[test]
fn gated_r2_peek_ufcs_fails_closed() {
    expect_r1_error_containing("gr2_peek_ufcs", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn liar_r2_touch_b_stale_fails_closed() {
    expect_r1_error_containing("lr2_touch_b_stale", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn liar_r2_touch_b_branch_fails_closed() {
    expect_r1_error_containing("lr2_touch_b_branch", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn liar_r2_touch_b_match_fails_closed() {
    expect_r1_error_containing("lr2_touch_b_match", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn liar_r2_touch_b_block_fails_closed() {
    expect_r1_error_containing("lr2_touch_b_block", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn liar_r2_touch_b_while_is_refused() {
    expect_r1_error_containing(
        "lr2_touch_b_while",
        SRC_R2_VALMUTREF,
        &[LOOP_RECEIVER_REFUSAL, "`s`"],
    );
}

#[test]
fn liar_r2_touch_b_for_is_refused() {
    expect_r1_error_containing(
        "lr2_touch_b_for",
        SRC_R2_VALMUTREF,
        &[LOOP_RECEIVER_REFUSAL, "`s`"],
    );
}

#[test]
fn liar_r2_touch_b_loop_is_refused() {
    expect_r1_error_containing(
        "lr2_touch_b_loop",
        SRC_R2_VALMUTREF,
        &[LOOP_RECEIVER_REFUSAL, "`s`"],
    );
}

#[test]
fn liar_r2_touch_b_while_invariant_is_refused() {
    expect_r1_error_containing(
        "lr2_touch_b_while_invariant",
        SRC_R2_VALMUTREF,
        &[LOOP_RECEIVER_REFUSAL, "`s`"],
    );
}

#[test]
fn liar_r2_touch_b_ref_param_ensures_is_rejected() {
    expect_r1_error_containing(
        "lr2_touch_b_ref_param_ensures",
        SRC_R2_VALMUTREF,
        &[MUT_STRUCT_POSTCONDITION_REJECT, "`r`"],
    );
}

#[test]
fn liar_r2_touch_b_nested_fails_closed() {
    expect_r1_error_containing("lr2_touch_b_nested", SRC_R2_VALMUTREF, &[UNRESOLVED, "`w`"]);
}

#[test]
fn liar_r2_touch_b_ufcs_fails_closed() {
    expect_r1_error_containing("lr2_touch_b_ufcs", SRC_R2_VALMUTREF, &[UNRESOLVED, "`s`"]);
}

#[test]
fn liar_r2_touch_b_return_field_fails_closed() {
    expect_r1_error_containing(
        "lr2_touch_b_return_field",
        SRC_R2_VALMUTREF,
        &[UNRESOLVED, "`s`"],
    );
}

#[test]
fn control_r2_getter_beside_impl_verifies() {
    expect_r1_verified("cr2_getter_beside_impl", SRC_R2_VALMUTREF);
}

#[test]
fn control_r2_shared_ref_by_value_verifies() {
    expect_r1_verified("cr2_shared_ref_by_value", SRC_R2_VALMUTREF);
}

#[test]
fn control_r2_peek_loop_local_verifies() {
    expect_r1_verified("cr2_peek_loop_local", SRC_R2_VALMUTREF);
}

#[test]
fn control_r2_peek_ensures_by_value_param_verifies() {
    expect_r1_verified("cr2_peek_ensures_by_value_param", SRC_R2_VALMUTREF);
}
