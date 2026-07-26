# Design: caller-side trait-method `requires` discharge (Phase-3 #7, unit 1)

**Status:** unit-1 spec (2026-06-04). Synthesized by a design judge-panel over the
trust-vc trait subsystem + Verus SMT semantics (pin `a40d57c7`), every load-bearing
claim verified against the code.

## The gap (a real unsoundness, not a missing feature)

The trait-spec machinery is already wired end-to-end: a trait method becomes an
uninterpreted function `T__method(self:Poly, params…)` (`declare_trait_method`); its
postcondition axiom `forall self,params {T__method(self,params)} . AND(requires) ==>
AND(ensures)` is asserted (`assert_trait_postconditions`, `trait_encoding_axioms.rs:183`);
concrete impls are linked (`T__method(Box_S(s),…)==S_method(…)`); generic-bound dispatch
lowers `z.f(args)` (`z: TypeParam(P)`, `P: T`) to `FnCall{T__f, [z,args]}`
(`ir_lowering/dispatch/methods.rs:245` + `prepared_context/type_env.rs:128` via
`register_trait_bound_methods_for_bounds`). `verify_trait_conformance` separately checks
each impl satisfies the contract.

**But:** at a generic trait-bounded call `z.f(args)` the method's `requires` is consumed
ONLY as the antecedent of the *assumed* postcondition axiom. **The caller is never made to
prove the precondition.** `record_helper_contract_call` fires only on `syn::ExprCall` (path
form, `body_extract.rs:1753`); `MethodCall`s emit no obligation. Relative to Verus
(`assert req%T.f(args)` at `StmX::Call`, `sst_to_air.rs:1925`) this is **strictly more
permissive** for any requires-bearing trait method called generically — an unsoundness.
(Sound for requires-free methods, which dominate the current corpus.)

## The fix (unit 1) — purely additive, requires-only

At a body `MethodCall` whose receiver resolves to a bounded `TypeParam` and whose trait
method has a non-empty `requires`, emit ground `__call_requires_{T__f}_{call_index}_{i}`
`ProofObligation::assert`s — `self := receiver`, `param_i := arg_i` — reusing the audited
`parse_helper_contract_expr` + `substitute_helper_contract_clause` path verbatim. Ensures
keeps flowing only from the existing global postcondition axiom (requires-only; no
site-local `__call_ensures_*`). NO new SMT/axiom/UF/MBQI — pure obligation generation over
the existing ground + single-trigger e-matching encoding.

**Soundness:** purely additive in the goal direction (adds an assert, weakens/removes
nothing). Adding a goal can only move a verdict from Verified toward NotVerified — never the
reverse — so it cannot make trust-vc prove MORE than before, and in particular moves it from
*more-permissive-than-Verus* toward parity. For abstract `A: T`, `T__req(a)` is an
uninterpreted app with no defining fact → assert unprovable → fail-closed; for a concrete
impl the linking axiom grounds it → dischargeable. Asserts fail CLOSED on Unknown.

## File-by-file plan

1. `vc_extraction/trait_contracts.rs`: pure helper `trait_bound_method_requires(trait_bounds,
   trait_decls) -> BTreeMap<(type_param, method), TraitMethodCallContract>`; for each
   `TraitBound{type_param, trait_name}` find the `TraitDecl`, and for each method with a
   NON-EMPTY `requires` build `TraitMethodCallContract { receiver_binding:
   "self" (= TRAIT_RECEIVER_NAME), param_names: method.params names, requires:
   method.requires.clone(), uf_prefix: "{trait_name}__{method}" }`. No I/O / no `vc` mutation
   → independently unit-testable.
2. `vc_extraction/body_extract.rs`: define `struct TraitMethodCallContract {…}` near
   `HelperCallContract` (line ~145); add `trait_method_contracts:
   Option<&BTreeMap<(String,String), TraitMethodCallContract>>` + reuse
   `recorded_trait_method_contract_call_sites: BTreeSet<usize>` on `AssertionCollector`
   (mirror `helper_contracts`/`recorded_helper_contract_call_sites`); constructor threads the
   map, `None` by default everywhere else.
3. `vc_extraction/body_extract.rs`: `record_trait_method_contract_call(&mut self, mc:
   &ExprMethodCall)`: early-return if `parse_error` or map is None; dedup via `mc as *const _
   as usize`; receiver bare ident via `expr_path_ident` (else FALL THROUGH, no obligation);
   `let TrustVcType::TypeParam(p) = self.vc.get_variable_type(recv)?.clone() else { return }`;
   look up `(p, method)` (absent → return); arity-check vs `param_names` (mirror line ~1774);
   render scoped receiver + scoped args; call `add_trait_method_requires_obligations`.
4. `vc_extraction/body_extract.rs`: `add_trait_method_requires_obligations(&mut self,
   contract, receiver_string, arg_strings)`: `call_index = self.next_helper_call_contract_index;
   self.next_helper_call_contract_index += 1` (shared counter, no suffix collision); build
   substitutions `{ receiver_binding -> parse_helper_contract_expr(receiver_string,…) } ∪
   { param_name -> parse_helper_contract_expr(arg,…) }`; for each `(i, req_str)`: parse to
   `Expr`, `substitute_helper_contract_clause(...)`, push
   `ProofObligation::assert("__call_requires_{uf_prefix}_{call_index}_{i}", condition)`. No
   ensures. Reuse `substitute_helper_contract_clause`/`parse_helper_contract_expr` verbatim.
5. `vc_extraction/body_extract.rs`: in `visit_expr_method_call` (line ~3776), AFTER existing
   `assign_local_*`/`record_option_closure_contract_call` and BEFORE
   `self.visit_expr(&method_call.receiver)`, insert `self.record_trait_method_contract_call(
   method_call);` (guard `if self.parse_error.is_some() { return; }`). This is the TRUE
   chokepoint catching both `a.f();` (`Stmt::Expr`) and `let _g = a.f();` (`Stmt::Local`
   init). **Do NOT hook `format_method_call_expr` (line ~1905) — rendering-only, NOT reached
   for discarded statements.**
6. `vc_extraction.rs`: in `extract_verification_conditions_from_parts`, after
   `apply_function_trait_bounds` + trait-decl registration, build
   `trait_method_call_contracts = trait_bound_method_requires(fc.trait_bounds(),
   vc.trait_decls())` (clone owned `TraitBound`/`TraitDecl` data out of `vc` first to dodge the
   borrow conflict); thread it alongside `sibling_helper_contracts` into a unified
   `extract_body_assertions_with_helper_and_trait_method_contracts(...)`; keep the no-contracts
   fast path.
7. Tests: `vc_extraction/tests/control_flow_assertions.rs` — the FAIL + VERIFY pair (below),
   modeled on `test_sibling_helper_requires_is_checked_at_call_site` (line ~1584).
   `trait_contracts.rs` tests module — the pure-helper unit test.

## Unit lib tests

- **FAIL** `test_generic_trait_method_requires_is_checked_at_call_site`: trait `T { spec fn
  req(&self)->bool; #[requires(self.req())] fn f(&self); }`, `impl T for S`, and
  `#[ensures(true)] fn test2<A: T>(a: &A) { a.f(); }`. Assert (1) an obligation
  `name.starts_with("__call_requires_T__f_") && condition.contains("req")` exists (it currently
  produces ZERO) and the condition does NOT contain bare `self` (proves `self := a`
  substitution); (2) `verify()` is NOT `Verified` (abstract `T__req(a)` unestablished →
  fail-closed, matching Verus `test_verify_5`).
- **VERIFY** `test_generic_trait_method_requires_discharges_when_established`: same trait/impl,
  caller `#[requires(a.req())] #[ensures(true)] fn test1<A: T>(a: &A) { a.f(); }`. Assert the
  obligation still EXISTS and `verify()` IS `Verified` (the caller's own `requires` supplies the
  matching `T__req(a)` hypothesis). Pins the obligation is real + dischargeable (not dead/vacuous).
- **PURE** `test_trait_bound_method_requires_maps_requires_bearing_methods` (trait_contracts.rs):
  `TraitBound("A","T")` + `TraitDecl T` with `f` (requires `["self.req()"]`) and `req` (empty
  requires) → map has `("A","f")` with `receiver_binding=="self"`, `uf_prefix=="T__f"`, right
  `param_names`, raw requires string; and NO `("A","req")` entry (fail-closed scope).

## Risks / discipline

- **Hook placement**: MUST be `visit_expr_method_call`, NOT `format_method_call_expr`
  (rendering-only, misses discarded statements). The FAIL test uses `a.f();` to catch this.
- **`self` substitution**: `self` is NOT in `TraitMethodDecl.params`; add it as an explicit
  `receiver_binding -> receiver_expr` entry. FAIL test asserts no bare `self` survives.
- **Fall-through is conservative**: non-bare-ident receiver, non-`TypeParam` type (incl. the
  ≤2-char-uppercase TypeParam heuristic missing `Item`/`Self2` — pre-existing permissive gap,
  not new), absent map entry, concrete receiver `s.f()`, qualified `<S as T>::f`, assoc
  types/supertraits/multi-bound/default-body → emit NO obligation. A missed obligation is
  conservative; a guessed one is not.
- **Borrow conflict** in `vc_extraction.rs`: clone `TraitBound`/`TraitDecl` data out before the
  `&mut vc` body-extract borrow.
- **Suffix collision**: reuse `next_helper_call_contract_index` (shared) so trait + path-form
  names never collide.
- **Flip triage (critical)**: adding the obligation can flip an existing test that currently
  (unsoundly) verifies a generic trait-bounded call without discharging a precondition. A flip
  is MOST LIKELY a previously-masked unsoundness correctly tightened — but each must be
  confirmed individually, never blindly re-pinned or reverted. Likewise check no `ported`
  corpus entry was relying on the permissiveness (if one was, it was a FALSE verification and
  un-promoting it is the correct, integrity-positive outcome).
- **Out of first-unit scope** (deliberate follow-ups): concrete-receiver discharge (Verus
  `test_verify_1`), robust TypeParam resolution from signature type-params, multi-bound
  conflict handling, requires referencing a defaulted spec method.

---

# Unit 2: concrete-receiver trait-method `requires` discharge

**Status:** unit-2 spec (2026-06-05). Same unsoundness class as unit 1, for CONCRETE
receivers. Confirmed gap (design workflow, 3/4 readers): `s.f(args)` where `s: S`,
`impl T for S`, `T::f` has non-empty `requires` — no caller-side obligation is emitted
(unit-1's `record_trait_method_contract_call` early-returns at `let TrustVcType::TypeParam(..)
else { return }`; a concrete `S` is `Datatype`/`Opaque`, not `TypeParam`). Verus emits
`assert req%T.f(args)` unconditionally (`sst_to_air.rs` StmX::Call) — it FAILS `test_verify_1`/
`test_verify_3` (`requires false`) where trust-vc silently verifies. Dormant today (0 ported
entries use requires-bearing trait methods on concrete receivers) but real.

## Fix — mirror unit 1, concrete-type-keyed

1. `trait_contracts.rs`: new pure builder `concrete_impl_method_requires(trait_impl_decls:
   &[TraitImplDecl], trait_decls: &[TraitDecl]) -> BTreeMap<(String /*concrete type name*/,
   String /*method*/), TraitMethodCallContract>`, placed after `trait_bound_method_requires`.
   - **CORRECTION vs the raw design plan:** do NOT skip on `concrete_type.contains_opaque()` —
     a concrete struct `S` parses to `Opaque("S")`, and `contains_opaque()` would wrongly reject
     it. Instead skip impls whose `concrete_type` **contains a `TypeParam`** (generic impl, v1
     out of scope). Add a small local `fn type_contains_type_param(&TrustVcType) -> bool`
     (recursing Seq/Array/Set/Multiset/Map/SpecFn/Datatype fields, true for `TypeParam`).
   - `let type_name = impl_decl.concrete_type.to_type_string();` (the KEY; the receiver side
     uses the same `to_type_string()` so they match; a mismatch fails closed — a missed
     obligation, conservative).
   - find the `TraitDecl` by `impl_decl.trait_name` (skip if absent); for each
     `(trait_method_name, _concrete_fn)` in `impl_decl.method_bindings`, find the
     `TraitMethodDecl` by name; skip if `method.requires.is_empty()` (fail-closed scope);
     build the IDENTICAL `TraitMethodCallContract` as unit 1 with `uf_prefix =
     "{trait}__{method}"` (the TRAIT name, so it routes through the linked `T__f` UF).
   - **Ambiguity drop:** track `source_trait: BTreeMap<(type,method), trait_name>`. If a
     `(type,method)` key is supplied by a DIFFERENT trait, `map.remove(key)` and mark it
     `ambiguous` so it is never re-inserted (a struct impl'ing two traits each with a
     requires-bearing `f` → NO `(S,f)` entry; missed requires is conservative, wrong-trait
     requires is a spurious failure). Same-trait re-registration is idempotent (keep).
2. `body_extract.rs`: add `concrete_method_contracts: Option<&'a BTreeMap<(String,String),
   TraitMethodCallContract>>` + `recorded_concrete_method_contract_call_sites: BTreeSet<usize>`
   to `AssertionCollector`; thread through `new_inner`, `new_with_helper_and_trait_method_
   contracts`, and the struct literal (default `None`/empty). Widen the public entry
   `extract_body_assertions_with_helper_and_trait_method_contracts` with the new
   `Option<&...>` param. In `record_trait_method_contract_call`, **refactor the lookup→emit
   tail into a shared helper** `fn discharge_trait_method_requires(&mut self, mc, contract)`
   taking a resolved `&TraitMethodCallContract`; the existing `TypeParam` arm fetches from the
   generic map, and a NEW arm (when the receiver type is NOT a `TypeParam`) fetches from the
   concrete map keyed by `receiver_ty.to_type_string()`. Both arms reuse the unchanged
   `add_trait_method_requires_obligations` + the shared `next_helper_call_contract_index`
   counter (no name collision). Keep the existing fail-closed guards (bare-ident receiver,
   known type, arity check).
3. `vc_extraction.rs`: after `trait_decls_owned`, add `let trait_impl_decls_owned =
   vc.trait_impl_decls().to_vec();` and `let concrete_method_call_contracts =
   trait_contracts::concrete_impl_method_requires(&trait_impl_decls_owned, &trait_decls_owned);`.
   Add `&& concrete_method_call_contracts.is_empty()` to the fast-path guard; pass
   `(!…is_empty()).then_some(&concrete_method_call_contracts)` as the new trailing arg.

## Tests (deterministic-first)

- PURE builder `test_concrete_impl_method_requires_maps_requires_bearing_method`: `TraitDecl T`
  with `f`(requires `["self.req()"]`) + `req`(no requires), `TraitImplDecl::new("T",
  Opaque("S"), [("f","S__f"),("req","S__req")])` → map has `("S","f")` (receiver_binding "self",
  uf_prefix "T__f", raw requires, empty params); NO `("S","req")`.
- PURE ambiguity `test_concrete_impl_method_requires_drops_ambiguous_trait_selection`: two
  traits `T`,`U` each with requires-bearing `f`, two impls both for `S` → NO `("S","f")` entry.
  Plus: a generic impl (`concrete_type` containing a `TypeParam`) is SKIPPED.
- WIRED obligation-count (robust to solver non-determinism — assert COUNT not verdict): a
  fixture `fn t(){ let s = S{}; s.f(); }` with `impl T for S`, `T::f` requires → emits EXACTLY
  ONE `__call_requires_T__f_*`; a fall-through fixture (empty requires / ambiguous / unregistered)
  emits ZERO. Optionally a FAIL-verdict test if the impl spec-fn body axiom is reliably emitted.

## Soundness / fall-through (identical posture to unit 1)

Purely additive in the goal direction — adds only `assert` goals, weakens nothing — so it can
only move Verified→NotVerified, never the reverse. `uf_prefix` = trait name routes through the
encoder's unconditional linking axiom `T__req(Box_S(s)) == S__req(s)` + the impl spec-fn body
axiom, so the assert means exactly Verus's `assert req%T.f`. Worst case is a SPURIOUS failure
(over-restrictive), prevented in the one ambiguity case by the drop. Fall-through (no obligation)
for: non-bare-ident receiver, unknown receiver type, TypeParam receiver (unit-1 arm), no map
entry, empty requires, ambiguous trait, generic impl, unregistered trait, `to_type_string`
key mismatch (`&S` vs `S`, etc. — known conservative v1 limitation). Arity mismatch is the one
hard error (mirrors unit 1).

---

# Unit 3: inherent (non-trait) method `requires` discharge

**Status:** unit-3 spec (2026-06-05). Found by the requires-discharge completeness audit — a
genuine UNSOUND gap of the same class as units 1/2, and the simplest remaining one.

**The gap:** `x.m(args)` where `x: S` and `impl S { #[trust_vc::proof] #[requires(..)] fn
m(&self,..) }` (NO trait). Inherent impl methods ARE discovered + verified as callees
(function_discovery.rs), so `m`'s `requires` is ASSUMED at `m`'s entry but NEVER asserted at
any call site — the textbook caller/callee asymmetry → `caller()` is silently Verified where
Verus emits `assert req%S.m` (StmX::Call makes no inherent-vs-trait distinction). It sits in the
seam between the three closed units: it's a `MethodCall` (so the `Expr::Call` helper path never
fires) but has NO trait (so `parse_trait_impl_decl` hard-errors on inherent impls → they never
enter `trait_impl_decls` → the unit-2 concrete map is structurally empty for them).

**Simpler than unit 2:** an inherent requires references the receiver's OWN concrete fields/spec
methods (`self.v > 0` → ground `s.v > 0`), so there is NO dependence on the `T__req(Box_S(s)) ==
S__req(s)` linking axiom unit 2 needs. The obligation is a plain ground condition.

## Fix (reuse units 1/2 verbatim; only a new builder + a merge)

1. `trait_contracts.rs`: new pure `inherent_impl_method_requires(items: &[syn::Item]) ->
   TrustVcResult<BTreeMap<(String,String), TraitMethodCallContract>>` mirroring
   `concrete_impl_method_requires`. Walk `Item::Impl` with `trait_.is_none()` (recurse modules);
   skip generic self via `type_has_nested_type_param`; `type_name` from the impl `self_ty` via the
   SAME derivation the concrete builder + receiver resolution use (`to_type_string()`); for each
   `ImplItem::Fn`, `let (requires, _) = extract_contracts(&method.attrs, "proof")?` (surface arg
   only affects error text); skip empty requires; `receiver_binding="self"`, `param_names` from
   non-`Receiver` inputs, `uf_prefix = "{type_name}__{method}"` (a NAME only). Ambiguity/collision
   with a concrete-trait `(S,m)` key → DROP (or trait-precedence) — never emit a wrong requires.
2. `vc_extraction.rs`: build the inherent map from `file.items` (independent of the trait gate —
   inherent impls aren't trait impls) and MERGE into `concrete_method_call_contracts` (with
   collision handling) so the existing `other =>` dispatch arm in `record_trait_method_contract_call`
   resolves inherent receivers with ZERO body_extract change. Update the empty-check + `.then_some`.
3. Tests: pure builder test (maps requires-bearing inherent method; empty-requires → none; trait
   impl ignored) + the MANDATORY real-path firing test below + positive-verify + fall-through.

## Mandatory real-path firing test (the unit-2 lesson)

`test_inherent_method_requires_is_checked_at_call_site`: source `struct S { v: i32 } impl S {
#[trust_vc::proof] #[requires(self.v > 0)] fn m(&self) {} } #[trust_vc::ensures(true)] fn
caller(s: S) { s.m(); }`, drive `extract_verification_conditions_with_file_context`, assert
EXACTLY ONE `Assert` obligation `name.starts_with("__call_requires_S__m_")`, condition contains
`v`, `self := s` (no bare self), token `s` present. MUST pass (proves WIRED, not dead). Also run
`targo test -p trust-vc-core --lib trait_method_requires` to confirm unit-1/2 emission unperturbed.

## Soundness / fall-through

Purely additive in the goal direction (adds only `assert` goals) — matches Verus's unconditional
caller-side assert; never more permissive. Fall-through (no obligation): generic inherent impl
(nested TypeParam), empty requires, non-bare-ident receiver, unresolved receiver type, key
collision (dropped). Hard error (fail-closed VerifyResult::Error): arity mismatch, unparsable
requires, malformed contract attr. OUT OF SCOPE (distinct gaps, must not be silently mis-handled):
qualified `S::m(&s)` Expr::Call form; operator-trait, default/supertrait, multi-bound/UFCS gaps.

---

# Unit 4: qualified UFCS `<S as T>::f(s, args)` requires discharge

**Status:** unit-4 spec (2026-06-05). Cleanest of the four remaining requires-discharge gaps
(completeness audit): highest reuse, smallest surface, ZERO IR/encoder/desugaring/vc_extraction
change — body_extract.rs + a test only.

**The gap:** `<S as T>::f(s, args)` is an `Expr::Call` whose `func` is an `Expr::Path` with
`qself.is_some()`. `visit_expr_call` routes every `Expr::Call` only to `record_helper_contract_call`
→ `source_call_reference_from_expr_path`, which returns `None` the moment `qself.is_some()` → bails
silently. The concrete-receiver discharge (`record_trait_method_contract_call`) is reached only from
`visit_expr_method_call` (the `s.f()` sugar), never for `Expr::Call`. So the UFCS form of the SAME
`(S, f)` the unit-2 concrete map keys emits zero `req%` obligations, while Verus emits the
unconditional `assert req%T.f` at StmX::Call for the UFCS kind too.

**Fix (reuses everything; body_extract.rs only):** new
`record_qualified_trait_fn_contract_call(&mut self, call: &syn::ExprCall)`: for `call.func` =
`Expr::Path` with `qself.is_some()`, derive `type_name = parse_or_opaque(extract_type_string(qself.ty)).to_type_string()`
(the concrete type is named EXPLICITLY by `qself.ty` — no `get_variable_type`, no generic
substitution), `method = last path segment ident`, look up `(type_name, method)` in the EXISTING
`self.concrete_method_contracts` (already populated + threaded), arity-check `call.args.len() ==
param_names.len() + 1` (the +1 is the explicit self/receiver arg), and on a hit push one
`__call_requires_{T__f}_*` assert per requires clause with `self := scoped(args[0])`,
`param_i := scoped(args[1+i])`, reusing `add_trait_method_requires_obligations` verbatim. New
`recorded_qualified_trait_fn_call_sites: BTreeSet<usize>` dedup set (keyed `call as *const _ as
usize`). Hook in `visit_expr_call` / `record_helper_contract_call` neighborhood so it does NOT
consume the helper dedup set for a qself call.

**Mandatory real-path firing test** `test_qualified_ufcs_trait_method_requires_is_checked_at_call_site`:
mirror the committed unit-2 test but caller body `fn caller(s: S) { <S as T>::f(&s); }`; drive
`extract_verification_conditions_with_file_context`; assert exactly one `__call_requires_T__f_*`
Assert obligation with `self := s` (the `&s` receiver rendered, no bare self). Confirms WIRED.

**Soundness:** purely additive in the goal direction (adds only assert goals → toward Verus parity,
never more permissive). Fall-through (no obligation): `qself.is_none()` (plain/`S::f` non-qualified —
unchanged helper path); concrete map None; `(type,method)` absent (generic `<P as T>::f`
type-param → intentionally fail-closed); qself.ty/segment missing; dedup. Hard error: arity mismatch,
unparsable requires. Scope: ONLY the concrete-qself form keyed in the unit-2 map; generic-qself is
fail-closed. Remaining requires-discharge gaps after this (each its own unit): default-method-on-
concrete (unit-2 builder omits non-overridden inherited defaults from method_bindings), supertrait
(needs a TraitDecl supertrait field), operator-form `a + b` (needs operator→trait-method desugaring),
and the secondary finding that a `#[requires]` written directly on a trait-IMPL method is dropped.

---

# Unit 5: trait DEFAULT-method-on-concrete `s.d()` requires discharge

**Status:** unit-5 spec (2026-06-05). From the completeness audit. Unit 1 covers GENERIC default
calls (`z.d()`, z:TypeParam) because `trait_bound_method_requires` iterates `trait_decl.methods`
(which includes default-bodied methods with their requires). Unit 2's concrete map MISSES them: it
iterates `impl_decl.method_bindings`, which are built only from the `ImplItem::Fn` PHYSICALLY WRITTEN
in the impl block — a non-overridden inherited default `d` is absent → no `(S, d)` entry → `s.d()`
silently verifies while Verus emits `assert req%T.d`.

**Fix (one-line-ish in the unit-2 builder):** in `concrete_impl_method_requires` (trait_contracts.rs),
iterate `trait_decl.methods` directly (every requires-bearing method) instead of
`impl_decl.method_bindings`, keyed `(type_name, method.name)`. Rationale: a valid `impl T for S`
provides EVERY method of T (overridden → its binding; non-overridden → the trait default), and the
`requires` is the TRAIT's contract regardless of override — so `s.m()` for any requires-bearing `m`
of T must discharge `m`'s requires. Keep the generic-self skip (`type_has_nested_type_param`) and the
cross-trait ambiguity drop. This is purely additive (adds the previously-missing inherited-default
entries; the bound/overridden entries are unchanged since they're also in `trait_decl.methods`).

**Mandatory real-path firing test** `test_concrete_default_method_requires_is_checked_at_call_site`:
source `#[trust_vc::trait_spec] trait T { fn req(&self)->bool; #[trust_vc::requires(self.req())] fn
d(&self) {} }  struct S;  #[trust_vc::trait_impl] impl T for S { fn req(&self)->bool { true } /* d
NOT overridden */ }  #[trust_vc::ensures(true)] fn caller(s: S) { s.d(); }`; drive
`extract_verification_conditions_with_file_context`; assert exactly one `__call_requires_T__d_*`
Assert obligation with `self := s`. (Confirms the inherited default is now in the concrete map and
fires.) Plus: confirm the committed unit-2 concrete-OVERRIDDEN-method test still passes (the iteration
change must not drop bound-method entries).

**Soundness:** purely additive in the goal direction. Existing unit-1/2/3/4 tests must stay green
(0 flips). Out of scope (queued): supertrait, operator `a + b`, impl-method `#[requires]`.

---

# Unit 6: supertrait-method `requires` discharge (`trait T: Super`)

**Status:** unit-6 spec (2026-06-05, design rated yes-medium). A call `z.super_m()` (z:T, T:Super) or
`s.super_m()` (impl T for S, T:Super), where super_m has a requires declared on Super, is SILENTLY
DROPPED — neither requires builder ever sees Super's methods (TraitDecl carries no supertraits; the
`: Super` bound is unparsed). Verus emits an unconditional `assert req%Super.super_m`.

**Fix (medium, multi-file):**
1. `ir.rs`: add `pub supertraits: Vec<String>` to TraitDecl (keep `::new(name, methods)` 2-arg,
   init empty) + `#[must_use] pub fn with_supertraits(self, Vec<String>) -> Self`.
2. `trait_expand.rs`: parse `input.supertraits` in parse_trait_decl (mirror append_trait_bounds:
   TypeParamBound::Trait, modifier None, last path segment) → with_supertraits; AND round-trip the
   field in trait_decl_tokens (else macro-expanded decls lose supertraits and the discharge no-ops).
3. `trait_contracts.rs`: add `supertrait_closure_methods(trait_decls, start) -> Vec<(declaring_trait,
   &TraitMethodDecl)>` — start-first BFS over supertraits with a `visited` cycle guard and a
   `claimed` method-NAME guard (most-derived/nearest-to-start wins = Rust shadowing). Change the loop
   in BOTH trait_bound_method_requires and concrete_impl_method_requires to iterate the closure,
   using **declaring_trait** in `uf_prefix` (LOAD-BEARING: the encoder's linking axiom grounds
   `Super__super_m(Box_S(s)) == S__super_m(s)` keyed on the DECLARING trait) and in the source_trait
   ambiguity bookkeeping (so Super reached via both `impl T for S` and `impl Super for S` is
   idempotent, not a spurious drop). Keep empty-requires skip, generic-self skip, cross-trait drop.
4. `encoder/trait_encoding_axioms.rs`: add `supertraits: Vec::new()` to the trait_decl_for_env literal.
5. `encoder/.../cache/cache_canonical.rs` write_trait_decl: emit the supertraits in the fingerprint
   (else two decls differing only in supertraits collide on a stale cache entry — correctness hole).
6. ~10 in-crate `TraitDecl { name, methods }` struct literals (tests/fixtures): append
   `supertraits: Vec::new(),` (grep `TraitDecl {`; non-exhaustive doesn't shield in-crate literals).
7. `trust-vc-merge-contract/fixtures/api_surface/trust-vc-core.txt`: REGENERATE (use the official
   bless/regen mechanism, not a hand-guess) to include the new field + fn, else the merge gate fails.

**Mandatory real-path firing tests** (control_flow_assertions.rs, via extract_verification_conditions_
with_file_context): GENERIC `trait Super { #[trust_vc::requires(n>10)] fn super_m(&self,n:u64); }`,
`#[trait_spec] trait T: Super {}`, `impl Super for S{...}`, `#[trait_impl] impl T for S {}`,
`fn g<Z:T>(z:&Z){ z.super_m(5); }` → assert EXACTLY ONE obligation `name.starts_with(
"__call_requires_Super__super_m_")` (Super__, NOT T__ — proves declaring-trait keying) AND verify()
NOT Verified (5>10 unmet); a `_discharges_when_established` sibling (call `super_m(11)` or caller
requires) → same obligation + verify() Verified (proves live, not vacuous). CONCRETE `fn g(s:&S){
s.super_m(5); }` likewise.

**Soundness:** purely additive in the goal direction (supertrait requires were silently dropped; the
closure only ADDS goals → stricter, toward Verus parity). Fall-through: no supertraits (byte-identical
to today — preserves all existing firing tests), marker supertrait, empty requires, unknown supertrait
name (no decl → contributes nothing), unregistered `impl Super for S` (ungrounded UF → fail-closed
Unknown), `?Sized`/lifetime/`~const` bounds (skipped). Cycles made total by `visited`. OUT OF SCOPE
(flag, follow-on): a supertrait requires that itself CALLS a supertrait spec method needs the same
transitive expansion in type_env.rs register_trait_bound_methods_for_bounds (the n>10 fixture doesn't
exercise it). Remaining requires-discharge gap after this: operator `a+b`.
