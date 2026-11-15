// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guard for a CARDINAL false verify in Phase A3 associated-type projection
//! resolution: a signature type `<Q as P>::A` was rewritten to the bound of the
//! FIRST `#[trust_vc::trait_impl]` whose trait IDENT, assoc ident and
//! whitespace-stripped self type matched — so the text resolved to an impl the
//! program does not name.
//!
//! ## The mechanism
//!
//! `collect_assoc_projection_bindings` keyed each binding by
//! `trait_path.segments.last().ident` (trait type arguments, default
//! arguments and path qualification all dropped), walked every inline module
//! without recording where the impl lives, admitted `#[cfg]`-gated, blanket
//! and generic impls, and `AssocProjectionResolver::resolve` returned the first
//! `.find` hit. The seam in `vc_extraction.rs` applied it to every signature
//! regardless of which generic parameters were in scope at the target.
//!
//! So with `impl Tr<bool> for S { type X = u8; }` declared before
//! `impl Tr<u32> for S { type X = u16; }`, a parameter `x: <S as Tr<u32>>::X`
//! — a `u16` in Rust — was lifted at `u8`, and `x <= 255u16` VERIFIED. Stock
//! rustc compiles the plain-Rust shape and the function returns `false` at
//! `x = 300`.
//!
//! ## Measured before the fix
//!
//! Against the unfixed engine (`ee37bb64`'s A3 resolver,
//! `TRUST_VC_DISABLE_VC_CACHE=1`), 28 of the 48 tests below failed:
//!
//! * 24 LIAR functions across F1-F15 came back `Verified` on a claim stock
//!   rustc falsifies (21 through `verify_function_from_file`, plus the F14
//!   line-selected `a::f14_dup` and `Wrap::f14_dup` and the F15 macro key);
//! * the two exact-resolution witnesses `f1_u32_add_one` and `f1_u32_eq300`
//!   were `Unknown(VacuousTruth)` (their u16 values do not fit the u8 they were
//!   lifted at), and the declaration-order-reversed TRUE claim
//!   `f2_rev_bool_le255` was a spurious `Counterexample`;
//! * the root copy `f14_dup` (F14a) was `Verified` on a TRUE claim and is now a
//!   deliberate fail-closed pin: nothing distinguishes it from its
//!   token-identical `mod a` twin.
//!
//! The other 20 tests (the same-file controls, and `f2_rev_u32_le255`, refuted
//! only because the u16 impl happened to come first) already held.
//!
//! F14 and F15 close two holes that an earlier, uncommitted cut of this fix
//! still left open: it keyed on the full header but took the module scope from
//! the root-precedence identity lookup (the F14 liars were measured `Verified`
//! against that cut) and accepted macro text as a key.
//!
//! F16 and F17 close a hole the first COMMITTED cut (`66380aa7`) left open,
//! found by adversarial review: both identity lookups read the
//! duplicate-trait-PRUNED file, while `cargo trust-vc check` selects the target
//! by line in the unpruned one. A token-identical twin that is a default method
//! of a pruned trait was invisible to them, so the remaining candidates agreed
//! on a scope (F16) or on an impl's `Self` (F17) that the selected twin does
//! not have. Measured with `TRUST_VC_DISABLE_VC_CACHE=1`: at `66380aa7` the
//! line-selected liars `a::Q::f16_dup` (F16a, F16b) came back `Verified`, as
//! did their root twins, and the F16 controls held; with the F16 change alone
//! applied, F17a's twin pair (the same items, without the two distinct
//! controls) came back `Verified` for both copies while the unpruned F17b
//! layout already refused both. F16c is the reviewer's probe N1 in a file whose
//! pruned trait's own scope carries an attributed u16 binding: at `66380aa7`
//! both `n1_dup` copies came back `Verified`, and the distinct default methods
//! of the pruned `a::Q` were `OpaqueTypes` `Unknown` (the pruned walk found no
//! candidate for them at all).
//!
//! The second committed cut (`c2f6f843`) moved those two lookups onto the
//! unpruned file, and review round 2 refuted it: the target's OTHER lookups —
//! its inline module, which scopes consts and spec fns — still read the pruned
//! file, where a default method of a pruned trait has no copy and resolves
//! from the crate root. F18a is the reviewer's PZ2: `a::Q::pz2` reads `a::K ==
//! 9` and claims `result == 7u8`, with an unrelated `impl T { fn pz2(&self) }`
//! beside it. The pruned `Self` lookup had seen `(0 exact impls, 0 exact
//! non-impls, 1 same-named impl)` and refused; the unpruned one saw the target
//! as an exact non-impl and let it through, and `K` was read as the root's `7`:
//! `Err` (ambiguous `Self`) at `4cd7972e`, `Verified` at `c2f6f843`. F18b
//! (PZ3) is the projection-bearing form, `Err` then `Verified` too; F18c
//! (PZ2N, no impl twin) was `Verified` on both. So the extraction entry now
//! REFUSES a target when the duplicate-trait prune removed any source item with
//! its exact identity — the pruned trait's default methods and every item
//! token-identical to one — and every identity lookup reads the pruned file,
//! which after that check holds the complete candidate set. F16a/b/c and F17a
//! are re-pinned to that refusal, and F16c's distinct default methods of the
//! pruned `a::Q` (a refuted liar and a verified control at `c2f6f843`) are
//! refused too: the same position reads a module const as the root's.
//!
//! ## The rule these pins hold
//!
//! A projection is rewritten only when its text is guaranteed to denote exactly
//! the impl that binds it; otherwise it is left as written and fails closed
//! through the existing unrecognized-type `Unknown`:
//!
//! * SCOPE — every source item token-identical to the target (attributes,
//!   visibility, signature, body) sits in ONE inline module, with no root
//!   precedence (F14: `cargo trust-vc check` selects by line, so the lifted
//!   item may be any twin), and a target any of whose identical items sits in
//!   a trait the duplicate-trait prune removed is refused outright (F16-F18),
//!   so the candidates are counted over a file that holds all of them — for
//!   the scope and for the enclosing-impl `Self` that A3 may resolve through
//!   alike; that module path names exactly one inline module in
//!   the file (a `#[cfg]`-duplicated `mod a` does not); and only impls declared
//!   DIRECTLY in that module bind;
//! * MONOMORPHIC, UNGATED IMPL — no type/const generic params, no where-clause,
//!   no `default`, no `#[cfg]`/`#[cfg_attr]` or other rewriting attribute, on
//!   the impl or on the `type A = B` item (which also has no own generics);
//! * EXACT HEADER — the FULL trait path (qualification and generic arguments)
//!   and the self type compare equal as canonical token renderings, the assoc
//!   segment carries no arguments, and nothing mentions `Self` or a type macro
//!   (F15: `macro_rules!` is textually scoped);
//! * NO SHADOWING — neither the target signature nor the container of any
//!   identical item declares a type/const generic param or a where-clause;
//! * UNIQUE — exactly one admitted binding matches.
//!
//! Every fail-closed pin asserts the `OpaqueTypes` `Unknown` specifically
//! (never just `!Verified`; F17b asserts the ambiguous-`Self` extraction
//! refusal and F16-F18's pruned-trait pins the pruned-identity extraction
//! refusal instead) and sits in a fixture with a same-file control that
//! VERIFIES and one that REFUTES, so the closure is per projection and the
//! context is not vacuous. In F6, F14b and F16b a generic `S` shadows the
//! file's `struct S`, so the type-name rule refuses every `Verified` answer of
//! those files; their verifying controls pin that refusal, which only a
//! `Verified` answer can produce.

use std::sync::atomic::{AtomicUsize, Ordering};

use trust_vc_core::{
    extract_verification_conditions_with_file_context, resolve_function_at_line,
    verify_function_from_file, FunctionResolution, UnknownCategory, VerifyResult,
};

// ---------------------------------------------------------------------------
// Fixtures.
// ---------------------------------------------------------------------------

/// F1 — two impls of each parameterized trait for one self type, the NARROW
/// binding declared first. (Two attributed `Tr<_>` impls in one module do not
/// compile under the macros — E0428 on the generated helper — so this is the
/// file lane's shape; F4 is the compile-valid macro shape.)
const F1_TRAIT_ARGS: &str = r#"
#[trust_vc::trait_spec]
trait Tr<A> {
    type X;
}

#[trust_vc::trait_spec]
trait Sg<A> {
    type Y;
}

struct S;

#[trust_vc::trait_impl]
impl Tr<bool> for S {
    type X = u8;
}

#[trust_vc::trait_impl]
impl Tr<u32> for S {
    type X = u16;
}

#[trust_vc::trait_impl]
impl Sg<bool> for S {
    type Y = u8;
}

#[trust_vc::trait_impl]
impl Sg<u32> for S {
    type Y = i8;
}

#[trust_vc::ensures(result)]
fn f1_u32_returns_le255(x: <S as Tr<u32>>::X) -> bool {
    x <= 255u16
}

#[trust_vc::ensures(true)]
fn f1_u32_assert_ne300(x: <S as Tr<u32>>::X) {
    trust_vc::assert!(x != 300);
}

#[trust_vc::ensures(result)]
fn f1_sg_u32_nonneg(y: <S as Sg<u32>>::Y) -> bool {
    y >= 0
}

#[trust_vc::ensures(result <= 255u16)]
fn f1_u32_retproj_le255(x: <S as Tr<u32>>::X) -> <S as Tr<u32>>::X {
    x
}

#[trust_vc::ensures(result)]
fn f1_u32_nested_tuple_le255(x: (<S as Tr<u32>>::X, u8)) -> bool {
    x.0 <= 255
}

#[trust_vc::ensures(result)]
fn f1_bool_lt255(x: <S as Tr<bool>>::X) -> bool {
    x < 255u8
}

#[trust_vc::ensures(result)]
fn f1_bool_le255(x: <S as Tr<bool>>::X) -> bool {
    x <= 255u8
}

#[trust_vc::ensures(result)]
fn f1_u32_le65535(x: <S as Tr<u32>>::X) -> bool {
    x <= 65535u16
}

#[trust_vc::ensures(result)]
fn f1_sg_bool_nonneg(y: <S as Sg<bool>>::Y) -> bool {
    y >= 0u8
}

#[trust_vc::requires(x == 255u16)]
#[trust_vc::ensures(result == 256u16)]
fn f1_u32_add_one(x: <S as Tr<u32>>::X) -> <S as Tr<u32>>::X {
    x + 1u16
}

#[trust_vc::requires(x == 300u16)]
#[trust_vc::ensures(true)]
fn f1_u32_eq300(x: <S as Tr<u32>>::X) {
    trust_vc::assert!(x == 300u16);
}
"#;

/// F2 — the same traits with the WIDE binding declared first: the verdicts must
/// not depend on declaration order.
const F2_TRAIT_ARGS_REVERSED: &str = r#"
#[trust_vc::trait_spec]
trait Tr<A> {
    type X;
}

struct S;

#[trust_vc::trait_impl]
impl Tr<u32> for S {
    type X = u16;
}

#[trust_vc::trait_impl]
impl Tr<bool> for S {
    type X = u8;
}

#[trust_vc::ensures(result)]
fn f2_rev_bool_le255(x: <S as Tr<bool>>::X) -> bool {
    x <= 255u8
}

#[trust_vc::ensures(result)]
fn f2_rev_u32_le255(x: <S as Tr<u32>>::X) -> bool {
    x <= 255u16
}
"#;

/// F3 — a defaulted trait argument. `impl Tr for S` is `impl Tr<u32> for S`,
/// so the elided spelling denotes the u16 binding; the SPELLED `Tr<u32>` is a
/// different text for the same instance and stays unresolved (honest
/// incompleteness, never a guess).
const F3_DEFAULT_ARG: &str = r#"
#[trust_vc::trait_spec]
trait Tr<A = u32> {
    type X;
}

struct S;

#[trust_vc::trait_impl]
impl Tr<bool> for S {
    type X = u8;
}

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u16;
}

#[trust_vc::ensures(result)]
fn f3_elided_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f3_elided_le65535(x: <S as Tr>::X) -> bool {
    x <= 65535
}

#[trust_vc::ensures(result)]
fn f3_spelled_u32_le255(x: <S as Tr<u32>>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f3_bool_le255(x: <S as Tr<bool>>::X) -> bool {
    x <= 255u8
}

#[trust_vc::ensures(result)]
fn f3_bool_lt255(x: <S as Tr<bool>>::X) -> bool {
    x < 255u8
}
"#;

/// F4 — the compile-valid macro shape: only the narrow impl is attributed, the
/// wide one is plain Rust and invisible to the binding registry.
const F4_UNATTRIBUTED_WIDE_IMPL: &str = r#"
#[trust_vc::trait_spec]
trait Tq<A> {
    type X;
}

struct S;

#[trust_vc::trait_impl]
impl Tq<bool> for S {
    type X = u8;
}

impl Tq<u32> for S {
    type X = u16;
}

#[trust_vc::ensures(true)]
fn f4_u32_le255(x: <S as Tq<u32>>::X) {
    trust_vc::assert!(x <= 255u16);
}

#[trust_vc::ensures(true)]
fn f4_bool_le255(x: <S as Tq<bool>>::X) {
    trust_vc::assert!(x <= 255u8);
}

#[trust_vc::ensures(true)]
fn f4_bool_lt255(x: <S as Tq<bool>>::X) {
    trust_vc::assert!(x < 255u8);
}
"#;

/// F5a — a `#[cfg]`-disabled attributed impl beside the enabled plain impl.
const F5A_CFG_IMPL: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    type X;
}

#[trust_vc::trait_spec]
trait Tr2 {
    type X;
}

struct S;

#[cfg(any())]
#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

#[cfg(not(any()))]
impl Tr for S {
    type X = u16;
}

#[trust_vc::trait_impl]
impl Tr2 for S {
    type X = u8;
}

#[trust_vc::ensures(result)]
fn f5a_cfg_impl_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f5a_tr2_le255(x: <S as Tr2>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f5a_tr2_lt255(x: <S as Tr2>::X) -> bool {
    x < 255
}
"#;

/// F5b — `#[cfg]` on the two `type X` items of one attributed impl.
const F5B_CFG_ASSOC_ITEM: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    type X;
}

#[trust_vc::trait_spec]
trait Tr2 {
    type X;
}

struct S;

#[trust_vc::trait_impl]
impl Tr for S {
    #[cfg(any())]
    type X = u8;
    #[cfg(not(any()))]
    type X = u16;
}

#[trust_vc::trait_impl]
impl Tr2 for S {
    type X = u8;
}

#[trust_vc::ensures(result)]
fn f5b_cfg_item_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f5b_tr2_le255(x: <S as Tr2>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f5b_tr2_lt255(x: <S as Tr2>::X) -> bool {
    x < 255
}
"#;

/// F6 — generic parameters named `S` shadow the struct `S` at the use site. The
/// controls pin that NON-generic containers (a free fn, an inherent impl, a
/// generic-free trait's default method) still resolve.
const F6_SHADOWING_GENERICS: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    type X;
}

struct S;
struct W;
struct Wrap<T>(T);
struct Z;

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

impl Tr for W {
    type X = u16;
}

#[trust_vc::ensures(result)]
fn f6_fn_generic<S: Tr<X = u16>>(x: <S as Tr>::X) -> bool {
    x <= 255
}

impl<S: Tr<X = u16>> Wrap<S> {
    #[trust_vc::ensures(result)]
    fn f6_impl_generic(x: <S as Tr>::X) -> bool {
        x <= 255
    }
}

trait Q<S: Tr<X = u16>> {
    #[trust_vc::ensures(result)]
    fn f6_trait_generic(x: <S as Tr>::X) -> bool {
        x <= 255
    }
}

#[trust_vc::ensures(result)]
fn f6_free_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f6_free_lt255(x: <S as Tr>::X) -> bool {
    x < 255
}

impl Z {
    #[trust_vc::ensures(result)]
    fn f6_inherent_le255(x: <S as Tr>::X) -> bool {
        x <= 255
    }
}

trait R {
    #[trust_vc::ensures(result)]
    fn f6_trait_default_le255(x: <S as Tr>::X) -> bool {
        x <= 255
    }
}
"#;

/// F7 — a bounded blanket impl binds u8 for every `T: Foo`; `S` is not `Foo`
/// and binds u16, and a generic `T: Tr<X = u16>` projection must not be read
/// as the blanket's u8.
const F7_BLANKET_IMPL: &str = r#"
trait Foo {}

#[trust_vc::trait_spec]
trait Tr {
    type X;
}

struct S;
struct W;

impl Foo for W {}

#[trust_vc::trait_impl]
impl<T: Foo> Tr for T {
    type X = u8;
}

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u16;
}

#[trust_vc::ensures(result)]
fn f7_blanket_generic_le255<T: Tr<X = u16>>(x: <T as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f7_s_le65535(x: <S as Tr>::X) -> bool {
    x <= 65535
}

#[trust_vc::ensures(result)]
fn f7_s_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}
"#;

/// F8 — a local trait sharing its ident with `std::ops::Add`.
const F8_FOREIGN_TRAIT_SAME_IDENT: &str = r#"
#[trust_vc::trait_spec]
trait Add<Rhs> {
    type Output;
}

struct S;

#[trust_vc::trait_impl]
impl Add<u32> for S {
    type Output = u8;
}

impl std::ops::Add<u32> for S {
    type Output = u16;
    fn add(self, _rhs: u32) -> u16 {
        0u16
    }
}

#[trust_vc::ensures(result)]
fn f8_std_add_le255(x: <S as std::ops::Add<u32>>::Output) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f8_local_add_le255(x: <S as Add<u32>>::Output) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f8_local_add_lt255(x: <S as Add<u32>>::Output) -> bool {
    x < 255
}
"#;

/// F9 — module scope: the root `S` is `String`, not `a::S`.
const F9_MODULE_SCOPE: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

mod a {
    use super::Tr;

    pub struct S;

    #[trust_vc::trait_impl]
    impl Tr for S {
        type X = u8;
    }

    #[trust_vc::ensures(result)]
    pub fn f9_mod_le255(x: <S as Tr>::X) -> bool {
        x <= 255
    }

    #[trust_vc::ensures(result)]
    pub fn f9_mod_lt255(x: <S as Tr>::X) -> bool {
        x < 255
    }
}

pub use std::string::String as S;

impl Tr for S {
    type X = u16;
}

#[trust_vc::ensures(result)]
pub fn f9_root_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}
"#;

/// F10 — key rendering: `&'a mut S` and `&'amut S` are different types that
/// collapsed to one whitespace-stripped key.
const F10_KEY_RENDERING: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    type X;
}

struct S;

#[trust_vc::trait_impl]
impl<'a> Tr for &'a mut S {
    type X = u8;
}

impl<'amut> Tr for &'amut S {
    type X = u16;
}

#[trust_vc::ensures(result)]
fn f10_shared_ref_le255<'amut>(x: <&'amut S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f10_mut_ref_le255<'a>(x: <&'a mut S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f10_mut_ref_lt255<'a>(x: <&'a mut S as Tr>::X) -> bool {
    x < 255
}
"#;

/// F11 — a `#[cfg]`-duplicated module: both `mod a` blocks share one lexical
/// module path, but only the enabled one's impl is real. Comparing module
/// PATHS alone would let the disabled module's attributed u8 impl bind the
/// enabled module's projection (which rustc resolves to the plain u16 impl;
/// `a::f11_dup_mod_le255(300)` returns false).
const F11_CFG_DUPLICATED_MODULE: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

#[trust_vc::trait_spec]
pub trait Tr2 {
    type X;
}

pub struct S;
pub struct T;

#[cfg(any())]
mod a {
    use super::{Tr, S};

    #[trust_vc::trait_impl]
    impl Tr for S {
        type X = u8;
    }
}

#[cfg(not(any()))]
mod a {
    use super::{Tr, S};

    impl Tr for S {
        type X = u16;
    }

    #[trust_vc::ensures(result)]
    pub fn f11_dup_mod_le255(x: <S as Tr>::X) -> bool {
        x <= 255
    }
}

mod b {
    use super::{Tr2, T};

    #[trust_vc::trait_impl]
    impl Tr2 for T {
        type X = u8;
    }

    #[trust_vc::ensures(result)]
    pub fn f11_unique_mod_le255(x: <T as Tr2>::X) -> bool {
        x <= 255
    }

    #[trust_vc::ensures(result)]
    pub fn f11_unique_mod_lt255(x: <T as Tr2>::X) -> bool {
        x < 255
    }
}
"#;

/// F12 — `Self` in a trait default method is the IMPLEMENTOR, a generic; the
/// impl header's `Tq<Self>` is `Tq<S>`. Equal text, different instances.
/// (Stock rustc accepts this with the trait-level where-clause; for
/// `impl Q for W`, `f12_self_arg_le255(300)` returns false.)
const F12_SELF_IN_PROJECTION: &str = r#"
#[trust_vc::trait_spec]
pub trait Tq<A> {
    type X;
}

pub struct S;
pub struct W;

#[trust_vc::trait_impl]
impl Tq<Self> for S {
    type X = u8;
}

#[trust_vc::trait_impl]
impl Tq<W> for S {
    type X = u16;
}

pub trait Q: Sized
where
    S: Tq<Self, X = u16>,
{
    #[trust_vc::ensures(result)]
    fn f12_self_arg_le255(x: <S as Tq<Self>>::X) -> bool {
        x <= 255
    }
}

impl Q for W {}

#[trust_vc::ensures(result)]
pub fn f12_w_arg_le65535(x: <S as Tq<W>>::X) -> bool {
    x <= 65535
}

#[trust_vc::ensures(result)]
pub fn f12_w_arg_le255(x: <S as Tq<W>>::X) -> bool {
    x <= 255
}
"#;

/// F13 — a glob import shadowed by an explicit one. `mod a`'s `use super::*`
/// imports the root `S`, but `a`'s own `use std::string::String as S` shadows
/// it, so inside `a` the text `<S as Tr>::X` names `String`'s plain u16 impl,
/// not the root's attributed u8 impl (`a::f13_glob_shadow_le255(300)` returns
/// false). Equal text across modules is not identity even through a glob. (A
/// second `struct S` in `a` is already refused file-wide by the duplicate
/// type-name gate, so the shadow is a renaming import.)
const F13_GLOB_SHADOWED_SELF_TYPE: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub struct S;

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

#[trust_vc::ensures(result)]
pub fn f13_root_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
pub fn f13_root_lt255(x: <S as Tr>::X) -> bool {
    x < 255
}

mod a {
    use super::*;
    use std::string::String as S;

    impl Tr for S {
        type X = u16;
    }

    #[trust_vc::ensures(result)]
    pub fn f13_glob_shadow_le255(x: <S as Tr>::X) -> bool {
        x <= 255
    }
}
"#;

/// F14a — two TOKEN-IDENTICAL functions, one at the root and one in `mod a`,
/// where `S` names different types. Complete source-item identity (attributes,
/// visibility, signature, body) cannot tell them apart, and the module lookup
/// gives the root one precedence; so when `cargo trust-vc check` selects
/// `a::f14_dup` by its source LINE, a scope derived by precedence would resolve
/// `a`'s `<S as Tr>::X` (String's plain u16 impl; `a::f14_dup(300)` returns
/// false) against the root's attributed u8 impl.
const F14A_IDENTICAL_ITEM_OTHER_MODULE: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub struct S;

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

#[trust_vc::ensures(result)]
fn f14_dup(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f14a_root_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f14a_root_lt255(x: <S as Tr>::X) -> bool {
    x < 255
}

mod a {
    use super::Tr;
    pub use std::string::String as S;

    impl Tr for S {
        type X = u16;
    }

    #[trust_vc::ensures(result)]
    fn f14_dup(x: <S as Tr>::X) -> bool {
        x <= 255
    }
}
"#;

/// F14b — the same identity collision with a GENERIC container: the method's
/// `S` is `Wrap`'s type parameter (`Wrap::<W>::f14_dup(300)` returns false),
/// the root function's `S` is the struct.
const F14B_IDENTICAL_ITEM_GENERIC_CONTAINER: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub struct S;
pub struct W;
pub struct Wrap<T>(T);

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

impl Tr for W {
    type X = u16;
}

#[trust_vc::ensures(result)]
fn f14_dup(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f14b_root_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f14b_root_lt255(x: <S as Tr>::X) -> bool {
    x < 255
}

impl<S: Tr<X = u16>> Wrap<S> {
    #[trust_vc::ensures(result)]
    fn f14_dup(x: <S as Tr>::X) -> bool {
        x <= 255
    }
}
"#;

/// F15 — a type macro in the key. `macro_rules!` is TEXTUALLY scoped: the
/// second `pick` shadows the first from its definition onward, so the impl
/// header's `pick!()` is `S1` while the signature's `pick!()` is `S2`, whose
/// plain impl binds u16 (`f15_macro_self_le255(300)` returns false). Equal
/// macro text is not equal expansion.
const F15_TYPE_MACRO_IN_KEY: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

#[trust_vc::trait_spec]
pub trait Tr2 {
    type X;
}

pub struct S1;
pub struct S2;

macro_rules! pick {
    () => {
        S1
    };
}

#[trust_vc::trait_impl]
impl Tr for pick!() {
    type X = u8;
}

impl Tr for S2 {
    type X = u16;
}

#[trust_vc::trait_impl]
impl Tr2 for S1 {
    type X = u8;
}

macro_rules! pick {
    () => {
        S2
    };
}

#[trust_vc::ensures(result)]
fn f15_macro_self_le255(x: <pick!() as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f15_tr2_le255(x: <S1 as Tr2>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f15_tr2_lt255(x: <S1 as Tr2>::X) -> bool {
    x < 255
}
"#;

/// F16a — F14a's identity collision with the nested twin inside a trait the
/// engine PRUNES. `prune_shadowed_duplicate_traits` deletes a same-named trait
/// that no impl header names — `a::Q` here, since `impl Q for S` names the
/// root `Q` — and its default methods go with it. But `cargo trust-vc check`
/// resolves the target by line in the UNPRUNED file, so it can select
/// `a::Q::f16_dup`, whose `S` is `String` (`<Imp as a::Q>::f16_dup(300)`
/// returns false for any implementor `Imp`, which may live in another file or
/// crate). A scope walk over the pruned file saw only the root copy and
/// resolved the twin's projection against the root's attributed u8 impl.
const F16A_TWIN_IN_PRUNED_TRAIT: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub struct S;

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

pub trait Q {}

impl Q for S {}

#[trust_vc::ensures(result)]
fn f16_dup(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f16a_root_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f16a_root_lt255(x: <S as Tr>::X) -> bool {
    x < 255
}

pub mod a {
    use super::Tr;
    pub use std::string::String as S;

    impl Tr for S {
        type X = u16;
    }

    pub trait Q {
        #[trust_vc::ensures(result)]
        fn f16_dup(x: <S as Tr>::X) -> bool {
            x <= 255
        }
    }
}
"#;

/// F16b — F16a with a GENERIC pruned container: the twin's `S` is `a::Q`'s
/// type parameter (`<Imp as a::Q<W>>::f16_dup(300)` returns false), so the
/// pruned walk also lost the container's shadowing generic.
const F16B_TWIN_IN_PRUNED_GENERIC_TRAIT: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub struct S;
pub struct W;

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

impl Tr for W {
    type X = u16;
}

pub trait Q {}

impl Q for S {}

#[trust_vc::ensures(result)]
fn f16_dup(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f16b_root_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f16b_root_lt255(x: <S as Tr>::X) -> bool {
    x < 255
}

pub mod a {
    use super::Tr;

    pub trait Q<S: Tr<X = u16>> {
        #[trust_vc::ensures(result)]
        fn f16_dup(x: <S as Tr>::X) -> bool {
            x <= 255
        }
    }
}
"#;

/// F16c — the reviewer's probe N1 in a context that REFUTES: F16a's layout
/// with `a`'s `impl Tr for S { type X = u16; }` ATTRIBUTED, so the pruned
/// `a::Q`'s own scope carries a binding, plus two distinct default methods of
/// `a::Q`. At `c2f6f843` those resolved through `a`'s u16 binding (the liar
/// `f16c_q_le255` refuted, the true `f16c_q_le65535` verified), but the same
/// position read a module const as the root's (F18), so every default method
/// of the pruned `a::Q` is now refused, not only the token-identical `n1_dup`
/// pair. Ground truth: with an implementor `Imp` of `a::Q`,
/// `<Imp as a::Q>::n1_dup(300)` returns false.
const F16C_REVIEW_N1_WITH_REFUTING_SCOPE: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub struct S;

#[trust_vc::trait_impl]
impl Tr for S {
    type X = u8;
}

pub trait Q {}

impl Q for S {}

#[trust_vc::ensures(result)]
fn n1_dup(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f16c_root_le255(x: <S as Tr>::X) -> bool {
    x <= 255
}

#[trust_vc::ensures(result)]
fn f16c_root_lt255(x: <S as Tr>::X) -> bool {
    x < 255
}

pub mod a {
    use super::Tr;
    pub use std::string::String as S;

    #[trust_vc::trait_impl]
    impl Tr for S {
        type X = u16;
    }

    pub trait Q {
        #[trust_vc::ensures(result)]
        fn n1_dup(x: <S as Tr>::X) -> bool {
            x <= 255
        }

        #[trust_vc::ensures(result)]
        fn f16c_q_le255(x: <S as Tr>::X) -> bool {
            x <= 255
        }

        #[trust_vc::ensures(result)]
        fn f16c_q_le65535(x: <S as Tr>::X) -> bool {
            x <= 65535
        }
    }
}
"#;

/// F17 — F16's prune hiding a twin from the enclosing-impl `Self` lookup. The
/// inherent `S::f17_dup` and the default method `a::Q::f17_dup` are
/// token-identical; `a::Q` is pruned (`impl Q for S` names the root `Q`). Over
/// the pruned file the trait copy was invisible, so the line-selected trait
/// method counted as `S`'s method, its `Self` became `S`, and A3 resolved
/// `<S as Tr>::X` to `a`'s attributed u8 — but in `a::Q` `Self` is any
/// implementor with `X = u16` (`<W as a::Q>::f17_dup(300)` returns false).
const F17A_SELF_TWIN_IN_PRUNED_TRAIT: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub struct S;
pub struct W;

impl Tr for W {
    type X = u16;
}

pub trait Q {}

impl Q for S {}

pub mod a {
    use super::{Tr, S};

    #[trust_vc::trait_impl]
    impl Tr for S {
        type X = u8;
    }

    impl S {
        #[trust_vc::ensures(result)]
        fn f17_dup(x: <Self as Tr>::X) -> bool {
            x <= 255
        }

        #[trust_vc::ensures(result)]
        fn f17a_s_le255(x: <Self as Tr>::X) -> bool {
            x <= 255
        }

        #[trust_vc::ensures(result)]
        fn f17a_s_lt255(x: <Self as Tr>::X) -> bool {
            x < 255
        }
    }

    pub trait Q: Tr<X = u16> {
        #[trust_vc::ensures(result)]
        fn f17_dup(x: <Self as Tr>::X) -> bool {
            x <= 255
        }
    }
}
"#;

/// F17b — F17a with the trait NOT pruned (renamed `Q2`, implemented in the
/// file): the pair was already an ambiguous `Self` and fails closed. F17a must
/// fail closed too (it is refused one step earlier, at the prune check).
const F17B_SELF_TWIN_IN_UNPRUNED_TRAIT: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub struct S;
pub struct W;

impl Tr for W {
    type X = u16;
}

pub mod a {
    use super::{Tr, S, W};

    #[trust_vc::trait_impl]
    impl Tr for S {
        type X = u8;
    }

    impl S {
        #[trust_vc::ensures(result)]
        fn f17_dup(x: <Self as Tr>::X) -> bool {
            x <= 255
        }
    }

    pub trait Q2: Tr<X = u16> {
        #[trust_vc::ensures(result)]
        fn f17_dup(x: <Self as Tr>::X) -> bool {
            x <= 255
        }
    }

    impl Q2 for W {}
}
"#;

/// F18a — review round 2's PZ2, plus two root controls: a default method of the
/// PRUNED `a::Q` (`impl Q for S` names the root `Q`) reads `a::K == 9` and
/// claims `result == 7u8`; `impl T { fn pz2(&self) }` is an unrelated
/// same-named impl method. At `4cd7972e` the target was refused (ambiguous
/// `Self`: no exact candidate in the pruned file, one same-named impl); at
/// `c2f6f843` the unpruned `Self` lookup let it through and `K` was read in the
/// crate root's scope — `Verified`. Ground truth (`trustc --edition 2021
/// -Ztrust-verify=off`, `impl a::Q for Imp {}`): `<Imp as a::Q>::pz2()` returns
/// 9. The root controls show the root `K` IS 7, so the refusal is what keeps
/// the claim from being read there.
const F18A_PRUNED_DEFAULT_READS_MODULE_CONST: &str = r#"
pub const K: u8 = 7;

pub struct S;

pub trait Q {}

impl Q for S {}

pub struct T;

impl T {
    #[trust_vc::ensures(result)]
    fn pz2(&self) -> bool {
        true
    }
}

#[trust_vc::ensures(result == 7u8)]
fn f18a_root_k_eq7() -> u8 {
    K
}

#[trust_vc::ensures(result == 9u8)]
fn f18a_root_k_eq9() -> u8 {
    K
}

pub mod a {
    pub const K: u8 = 9;

    pub trait Q {
        #[trust_vc::ensures(result == 7u8)]
        fn pz2() -> u8 {
            K
        }
    }
}
"#;

/// F18b — review round 2's PZ3, the projection-bearing form of F18a: A3 scopes
/// `<R as Tr>::X` to `a` and resolves it to u16, while the body's `K` was read
/// as the root's `7`. `Err` at `4cd7972e`, `Verified` at `c2f6f843`; in Rust
/// `pz3(300)` is false. Root controls as in F18a.
const F18B_PRUNED_DEFAULT_PROJECTION_AND_MODULE_CONST: &str = r#"
#[trust_vc::trait_spec]
pub trait Tr {
    type X;
}

pub const K: u16 = 7;

pub struct S;

pub trait Q {}

impl Q for S {}

pub struct T;

impl T {
    #[trust_vc::ensures(result)]
    fn pz3(&self) -> bool {
        true
    }
}

#[trust_vc::ensures(result)]
fn f18b_root_k_or7(x: u16) -> bool {
    x != K || x == 7u16
}

#[trust_vc::ensures(result)]
fn f18b_root_k_ne(x: u16) -> bool {
    x != K
}

pub mod a {
    use super::Tr;

    pub const K: u16 = 300;

    pub struct R;

    #[trust_vc::trait_impl]
    impl Tr for R {
        type X = u16;
    }

    pub trait Q {
        #[trust_vc::ensures(result)]
        fn pz3(x: <R as Tr>::X) -> bool {
            x != K || x == 7u16
        }
    }
}
"#;

/// F18c — review round 2's PZ2N: F18a without the impl twin. `Verified` at
/// `4cd7972e` AND at `c2f6f843` (the pruned file has no copy of the target, so
/// its module scope was the crate root's); closed by the same refusal.
const F18C_PRUNED_DEFAULT_NO_TWIN: &str = r#"
pub const K: u8 = 7;

pub struct S;

pub trait Q {}

impl Q for S {}

#[trust_vc::ensures(result == 7u8)]
fn f18c_root_k_eq7() -> u8 {
    K
}

#[trust_vc::ensures(result == 9u8)]
fn f18c_root_k_eq9() -> u8 {
    K
}

pub mod a {
    pub const K: u8 = 9;

    pub trait Q {
        #[trust_vc::ensures(result == 7u8)]
        fn pz2() -> u8 {
            K
        }
    }
}
"#;

// ---------------------------------------------------------------------------
// Harness.
// ---------------------------------------------------------------------------

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

/// Every call gets its own file: tests run in parallel and several fixtures
/// reuse item names, so a shared path would let one test read another's source.
fn verdict(fixture: &str, src: &str, func: &str) -> VerifyResult {
    let seq = FIXTURE_SEQ.fetch_add(1, Ordering::SeqCst);
    let path = format!(
        "{}/assoc_projection_identity_{}_{fixture}_{seq}.rs",
        env!("CARGO_TARGET_TMPDIR"),
        std::process::id()
    );
    std::fs::write(&path, src).expect("write fixture");
    let result = verify_function_from_file(&path, func).unwrap_or_else(|e| VerifyResult::Error {
        message: format!("{e:?}"),
    });
    let _ = std::fs::remove_file(&path);
    result
}

/// The `cargo trust-vc check` lane: the target is selected by the source LINE of
/// its ident (`resolve_function_at_line`), which — unlike the bare-name lane's
/// root precedence — can select any one of several token-identical items. Picks
/// the `nth` (0-based) `fn {func}(` in `src`.
fn verdict_at_nth_definition(src: &str, func: &str, nth: usize) -> VerifyResult {
    let needle = format!("fn {func}(");
    let line = src
        .lines()
        .enumerate()
        .filter(|(_, text)| text.contains(&needle))
        .nth(nth)
        .map(|(index, _)| index + 1)
        .unwrap_or_else(|| panic!("fixture has no definition #{nth} of `{func}`"));
    let ast = trust_vc_core::parse_file_allow_tracked(src).expect("fixture parses");
    let target = match resolve_function_at_line(&ast, func, line) {
        FunctionResolution::Unique(target) => target,
        _ => panic!("`{func}` at line {line} is not exactly one item"),
    };
    extract_verification_conditions_with_file_context(&ast, target)
        .map(|ctx| ctx.verify())
        .unwrap_or_else(|e| VerifyResult::Error {
            message: format!("{e:?}"),
        })
}

fn assert_opaque_unknown(label: &str, v: &VerifyResult) {
    assert!(
        matches!(
            v,
            VerifyResult::Unknown {
                category: UnknownCategory::OpaqueTypes,
                ..
            }
        ),
        "{label}: expected a fail-closed OpaqueTypes Unknown (projection not provably the \
         named impl), got {v:?}"
    );
}

fn assert_verified(fixture: &str, src: &str, func: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "{fixture}::{func}: expected Verified (a TRUE claim over the exact binding), got {v:?}"
    );
}

/// A TRUE claim in a file with a generic spelled like one of its types, or
/// with a `use` that binds one of its type names to another type (`use
/// std::string::String as S;` beside `struct S`, which the lane reads by its
/// name in every module): the solver answers `Verified` and the type-name rule
/// turns only that answer into an `Error` carrying its tag.
fn assert_verified_then_type_name_refused(fixture: &str, src: &str, func: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(&v, VerifyResult::Error { message } if message.starts_with("type-name rebinding")),
        "{fixture}::{func}: expected the type-name rule's refusal of a Verified answer, got {v:?}"
    );
}

/// Stricter than `!Verified`: only a real refutation counts, so an extraction
/// error cannot pass for the refuted liar.
fn assert_refuted(fixture: &str, src: &str, func: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "{fixture}::{func}: expected a Counterexample (a FALSE claim), got {v:?}"
    );
}

/// Fail-closed pins must be the unrecognized-type `Unknown` (`OpaqueTypes`:
/// the projection was left unresolved and its variable cannot be encoded) —
/// not an `Error`, which would mean the target stopped being extracted for some
/// unrelated reason, and not a different `Unknown` (e.g. `VacuousTruth`), which
/// would mean the projection was resolved to SOMETHING.
fn assert_fails_closed(fixture: &str, src: &str, func: &str) {
    let v = verdict(fixture, src, func);
    assert_opaque_unknown(&format!("{fixture}::{func}"), &v);
}

// ---------------------------------------------------------------------------
// F1 — trait type arguments are part of the key.
// ---------------------------------------------------------------------------

/// LIAR (Verified before the fix; returns false at 300 in Rust).
#[test]
fn f1_u32_projection_is_u16_not_first_impls_u8() {
    assert_refuted("f1", F1_TRAIT_ARGS, "f1_u32_returns_le255");
}

/// LIAR (Verified before the fix).
#[test]
fn f1_u32_projection_reaches_300() {
    assert_refuted("f1", F1_TRAIT_ARGS, "f1_u32_assert_ne300");
}

/// LIAR (Verified before the fix): `<S as Sg<u32>>::Y` is i8, so -1 exists.
#[test]
fn f1_sg_u32_projection_is_signed() {
    assert_refuted("f1", F1_TRAIT_ARGS, "f1_sg_u32_nonneg");
}

/// LIAR (Verified before the fix): the RETURN position resolves exactly too.
#[test]
fn f1_return_position_projection_is_exact() {
    assert_refuted("f1", F1_TRAIT_ARGS, "f1_u32_retproj_le255");
}

/// LIAR (Verified before the fix): a projection nested in a tuple.
#[test]
fn f1_tuple_nested_projection_is_exact() {
    assert_refuted("f1", F1_TRAIT_ARGS, "f1_u32_nested_tuple_le255");
}

/// CONTROL: the u8 binding's upper value is reachable.
#[test]
fn f1_bool_projection_strict_bound_refutes() {
    assert_refuted("f1", F1_TRAIT_ARGS, "f1_bool_lt255");
}

#[test]
fn f1_bool_projection_u8_tautology_verifies() {
    assert_verified("f1", F1_TRAIT_ARGS, "f1_bool_le255");
}

#[test]
fn f1_u32_projection_u16_tautology_verifies() {
    assert_verified("f1", F1_TRAIT_ARGS, "f1_u32_le65535");
}

#[test]
fn f1_sg_bool_projection_unsigned_verifies() {
    assert_verified("f1", F1_TRAIT_ARGS, "f1_sg_bool_nonneg");
}

/// EXACT-RESOLUTION WITNESS (spurious non-Verified before the fix): 255 + 1
/// fits the u16 the projection denotes.
#[test]
fn f1_u32_projection_add_one_past_u8_verifies() {
    assert_verified("f1", F1_TRAIT_ARGS, "f1_u32_add_one");
}

/// EXACT-RESOLUTION WITNESS (VacuousTruth before the fix: 300 is not a u8).
#[test]
fn f1_u32_projection_holds_300_verifies() {
    assert_verified("f1", F1_TRAIT_ARGS, "f1_u32_eq300");
}

// ---------------------------------------------------------------------------
// F2 — declaration order is irrelevant.
// ---------------------------------------------------------------------------

/// TRUE claim that was a spurious Counterexample before the fix.
#[test]
fn f2_reversed_bool_projection_verifies() {
    assert_verified("f2", F2_TRAIT_ARGS_REVERSED, "f2_rev_bool_le255");
}

#[test]
fn f2_reversed_u32_projection_refutes() {
    assert_refuted("f2", F2_TRAIT_ARGS_REVERSED, "f2_rev_u32_le255");
}

// ---------------------------------------------------------------------------
// F3 — defaulted trait argument.
// ---------------------------------------------------------------------------

/// LIAR (Verified before the fix): elided `Tr` is `Tr<u32>`, the u16 impl.
#[test]
fn f3_elided_default_arg_projection_is_u16() {
    assert_refuted("f3", F3_DEFAULT_ARG, "f3_elided_le255");
}

#[test]
fn f3_elided_default_arg_u16_tautology_verifies() {
    assert_verified("f3", F3_DEFAULT_ARG, "f3_elided_le65535");
}

/// FAIL-CLOSED (Verified before the fix): the spelled default is a different
/// text; it is never guessed onto a binding.
#[test]
fn f3_spelled_default_arg_fails_closed() {
    assert_fails_closed("f3", F3_DEFAULT_ARG, "f3_spelled_u32_le255");
}

#[test]
fn f3_bool_controls() {
    assert_verified("f3", F3_DEFAULT_ARG, "f3_bool_le255");
    assert_refuted("f3", F3_DEFAULT_ARG, "f3_bool_lt255");
}

// ---------------------------------------------------------------------------
// F4 — compile-valid macro shape.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix): the binding for `Tq<u32>` is plain
/// Rust, so no attributed impl names this projection.
#[test]
fn f4_projection_bound_by_unattributed_impl_fails_closed() {
    assert_fails_closed("f4", F4_UNATTRIBUTED_WIDE_IMPL, "f4_u32_le255");
}

#[test]
fn f4_attributed_projection_controls() {
    assert_verified("f4", F4_UNATTRIBUTED_WIDE_IMPL, "f4_bool_le255");
    assert_refuted("f4", F4_UNATTRIBUTED_WIDE_IMPL, "f4_bool_lt255");
}

// ---------------------------------------------------------------------------
// F5 — `#[cfg]` gating.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix).
#[test]
fn f5a_cfg_gated_impl_does_not_bind() {
    assert_fails_closed("f5a", F5A_CFG_IMPL, "f5a_cfg_impl_le255");
}

#[test]
fn f5a_ungated_impl_controls() {
    assert_verified("f5a", F5A_CFG_IMPL, "f5a_tr2_le255");
    assert_refuted("f5a", F5A_CFG_IMPL, "f5a_tr2_lt255");
}

/// FAIL-CLOSED (Verified before the fix).
#[test]
fn f5b_cfg_gated_assoc_items_do_not_bind() {
    assert_fails_closed("f5b", F5B_CFG_ASSOC_ITEM, "f5b_cfg_item_le255");
}

#[test]
fn f5b_ungated_impl_controls() {
    assert_verified("f5b", F5B_CFG_ASSOC_ITEM, "f5b_tr2_le255");
    assert_refuted("f5b", F5B_CFG_ASSOC_ITEM, "f5b_tr2_lt255");
}

// ---------------------------------------------------------------------------
// F6 — generic parameters in scope shadow the key's names.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix; `f6_fn_generic::<W>(300)` is false).
#[test]
fn f6_fn_generic_shadowing_fails_closed() {
    assert_fails_closed("f6", F6_SHADOWING_GENERICS, "f6_fn_generic");
}

/// FAIL-CLOSED (Verified before the fix).
#[test]
fn f6_impl_generic_shadowing_fails_closed() {
    assert_fails_closed("f6", F6_SHADOWING_GENERICS, "f6_impl_generic");
}

/// FAIL-CLOSED (Verified before the fix).
#[test]
fn f6_trait_generic_shadowing_fails_closed() {
    assert_fails_closed("f6", F6_SHADOWING_GENERICS, "f6_trait_generic");
}

#[test]
fn f6_non_generic_scope_controls() {
    assert_verified_then_type_name_refused("f6", F6_SHADOWING_GENERICS, "f6_free_le255");
    assert_refuted("f6", F6_SHADOWING_GENERICS, "f6_free_lt255");
    assert_verified_then_type_name_refused("f6", F6_SHADOWING_GENERICS, "f6_inherent_le255");
    assert_verified_then_type_name_refused("f6", F6_SHADOWING_GENERICS, "f6_trait_default_le255");
}

// ---------------------------------------------------------------------------
// F7 — blanket impls never bind.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix; `f7_blanket_generic_le255::<S>(300)`
/// is false).
#[test]
fn f7_blanket_impl_does_not_bind_generic_projection() {
    assert_fails_closed("f7", F7_BLANKET_IMPL, "f7_blanket_generic_le255");
}

#[test]
fn f7_monomorphic_impl_controls() {
    assert_verified("f7", F7_BLANKET_IMPL, "f7_s_le65535");
    assert_refuted("f7", F7_BLANKET_IMPL, "f7_s_le255");
}

// ---------------------------------------------------------------------------
// F8 — the full trait path is part of the key.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix): `std::ops::Add` is not the local
/// `Add`.
#[test]
fn f8_foreign_trait_with_local_ident_fails_closed() {
    assert_fails_closed("f8", F8_FOREIGN_TRAIT_SAME_IDENT, "f8_std_add_le255");
}

#[test]
fn f8_local_trait_controls() {
    assert_verified("f8", F8_FOREIGN_TRAIT_SAME_IDENT, "f8_local_add_le255");
    assert_refuted("f8", F8_FOREIGN_TRAIT_SAME_IDENT, "f8_local_add_lt255");
}

// ---------------------------------------------------------------------------
// F9 — only impls in the target's own module bind.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix): root `S` is `String`.
#[test]
fn f9_other_modules_impl_does_not_bind() {
    assert_fails_closed("f9", F9_MODULE_SCOPE, "f9_root_le255");
}

#[test]
fn f9_same_module_controls() {
    assert_verified_then_type_name_refused("f9", F9_MODULE_SCOPE, "f9_mod_le255");
    assert_refuted("f9", F9_MODULE_SCOPE, "f9_mod_lt255");
}

// ---------------------------------------------------------------------------
// F10 — the self-type key keeps token boundaries.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix).
#[test]
fn f10_distinct_self_types_do_not_collide() {
    assert_fails_closed("f10", F10_KEY_RENDERING, "f10_shared_ref_le255");
}

#[test]
fn f10_exact_self_type_controls() {
    assert_verified("f10", F10_KEY_RENDERING, "f10_mut_ref_le255");
    assert_refuted("f10", F10_KEY_RENDERING, "f10_mut_ref_lt255");
}

// ---------------------------------------------------------------------------
// F11 — a module path must denote ONE module.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix; `a::f11_dup_mod_le255(300)` is false).
#[test]
fn f11_cfg_duplicated_module_does_not_bind() {
    assert_fails_closed("f11", F11_CFG_DUPLICATED_MODULE, "f11_dup_mod_le255");
}

#[test]
fn f11_unique_module_controls() {
    assert_verified("f11", F11_CFG_DUPLICATED_MODULE, "f11_unique_mod_le255");
    assert_refuted("f11", F11_CFG_DUPLICATED_MODULE, "f11_unique_mod_lt255");
}

// ---------------------------------------------------------------------------
// F12 — `Self` is never part of a resolvable key.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix; `<W as Q>::f12_self_arg_le255(300)`
/// is false).
#[test]
fn f12_self_in_trait_default_projection_fails_closed() {
    assert_fails_closed("f12", F12_SELF_IN_PROJECTION, "f12_self_arg_le255");
}

/// `f12_w_arg_le255` is itself a LIAR that was Verified before the fix: the
/// ident-keyed lookup took the first `Tq` impl for `S`, the `Tq<Self>` u8 one.
#[test]
fn f12_concrete_arg_controls() {
    assert_verified("f12", F12_SELF_IN_PROJECTION, "f12_w_arg_le65535");
    assert_refuted("f12", F12_SELF_IN_PROJECTION, "f12_w_arg_le255");
}

// ---------------------------------------------------------------------------
// F13 — a glob import does not carry a binding into a module that shadows it.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix): inside `a`, `S` is `String`.
#[test]
fn f13_glob_shadowed_self_type_does_not_bind() {
    assert_fails_closed("f13", F13_GLOB_SHADOWED_SELF_TYPE, "f13_glob_shadow_le255");
}

#[test]
fn f13_root_module_controls() {
    assert_verified_then_type_name_refused("f13", F13_GLOB_SHADOWED_SELF_TYPE, "f13_root_le255");
    assert_refuted("f13", F13_GLOB_SHADOWED_SELF_TYPE, "f13_root_lt255");
}

// ---------------------------------------------------------------------------
// F14 — token-identical items: identity cannot pick the scope, so nothing does.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix): `cargo trust-vc check` selects the
/// `mod a` copy by line; its `S` is `String`.
#[test]
fn f14a_line_selected_identical_item_in_other_module_fails_closed() {
    let v = verdict_at_nth_definition(F14A_IDENTICAL_ITEM_OTHER_MODULE, "f14_dup", 1);
    assert_opaque_unknown("f14a::a::f14_dup (line lane)", &v);
}

/// FAIL-CLOSED, honest incompleteness: the root copy's claim is true, but no
/// source-item witness distinguishes it from `a::f14_dup`, so its projection is
/// not resolved either.
#[test]
fn f14a_root_identical_item_fails_closed_too() {
    let v = verdict_at_nth_definition(F14A_IDENTICAL_ITEM_OTHER_MODULE, "f14_dup", 0);
    assert_opaque_unknown("f14a::f14_dup (line lane)", &v);
}

#[test]
fn f14a_distinct_item_controls() {
    assert_verified_then_type_name_refused(
        "f14a",
        F14A_IDENTICAL_ITEM_OTHER_MODULE,
        "f14a_root_le255",
    );
    assert_refuted("f14a", F14A_IDENTICAL_ITEM_OTHER_MODULE, "f14a_root_lt255");
}

/// FAIL-CLOSED (Verified before the fix): the line-selected method's `S` is
/// `Wrap`'s type parameter.
#[test]
fn f14b_line_selected_identical_item_in_generic_impl_fails_closed() {
    let v = verdict_at_nth_definition(F14B_IDENTICAL_ITEM_GENERIC_CONTAINER, "f14_dup", 1);
    assert_opaque_unknown("f14b::Wrap::f14_dup (line lane)", &v);
}

#[test]
fn f14b_distinct_item_controls() {
    assert_verified_then_type_name_refused(
        "f14b",
        F14B_IDENTICAL_ITEM_GENERIC_CONTAINER,
        "f14b_root_le255",
    );
    assert_refuted(
        "f14b",
        F14B_IDENTICAL_ITEM_GENERIC_CONTAINER,
        "f14b_root_lt255",
    );
}

// ---------------------------------------------------------------------------
// F15 — macro text never keys a binding.
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (Verified before the fix): the two `pick!()` expand in
/// different textual macro scopes.
#[test]
fn f15_type_macro_self_type_does_not_bind() {
    // The constant name and harness label read as a key assignment to Gitleaks.
    assert_fails_closed("f15", F15_TYPE_MACRO_IN_KEY, "f15_macro_self_le255"); // gitleaks:allow
}

#[test]
fn f15_plain_key_controls() {
    assert_verified("f15", F15_TYPE_MACRO_IN_KEY, "f15_tr2_le255");
    assert_refuted("f15", F15_TYPE_MACRO_IN_KEY, "f15_tr2_lt255");
}

// ---------------------------------------------------------------------------
// F16 — a target with an exact-identity copy the duplicate-trait prune removed
// is refused, so no identity lookup answers from the copies that survived.
// ---------------------------------------------------------------------------

/// The extraction-time refusal for a target the duplicate-trait prune removed a
/// copy of — a default method of a pruned trait, or an item token-identical to
/// one.
fn assert_pruned_identity_refusal(label: &str, v: &VerifyResult) {
    assert!(
        matches!(
            v,
            VerifyResult::Error { message }
                if message.contains("resolve target through duplicate-trait prune")
                    && message.contains("is set aside before verification")
        ),
        "{label}: expected the pruned-identity extraction refusal, got {v:?}"
    );
}

/// FAIL-CLOSED (Verified at `66380aa7`, whose scope walk read the pruned
/// file): the line-selected twin lives in the pruned `a::Q`.
#[test]
fn f16a_line_selected_twin_in_pruned_trait_fails_closed() {
    let v = verdict_at_nth_definition(F16A_TWIN_IN_PRUNED_TRAIT, "f16_dup", 1);
    assert_pruned_identity_refusal("f16a::a::Q::f16_dup (line lane)", &v);
}

/// FAIL-CLOSED, honest incompleteness (as F14a's root copy): the root claim is
/// true, but no identity tells it from its twin in the pruned `a::Q`.
#[test]
fn f16a_root_twin_of_pruned_trait_method_fails_closed_too() {
    let v = verdict_at_nth_definition(F16A_TWIN_IN_PRUNED_TRAIT, "f16_dup", 0);
    assert_pruned_identity_refusal("f16a::f16_dup (line lane)", &v);
    assert_pruned_identity_refusal(
        "f16a::f16_dup",
        &verdict("f16a", F16A_TWIN_IN_PRUNED_TRAIT, "f16_dup"),
    );
}

/// The prune leaves the file verifiable: distinct root items still resolve.
#[test]
fn f16a_distinct_item_controls() {
    assert_verified_then_type_name_refused("f16a", F16A_TWIN_IN_PRUNED_TRAIT, "f16a_root_le255");
    assert_refuted("f16a", F16A_TWIN_IN_PRUNED_TRAIT, "f16a_root_lt255");
}

/// FAIL-CLOSED (Verified at `66380aa7`): the line-selected twin's `S` is the
/// pruned generic trait's type parameter.
#[test]
fn f16b_line_selected_twin_in_pruned_generic_trait_fails_closed() {
    let v = verdict_at_nth_definition(F16B_TWIN_IN_PRUNED_GENERIC_TRAIT, "f16_dup", 1);
    assert_pruned_identity_refusal("f16b::a::Q::f16_dup (line lane)", &v);
}

#[test]
fn f16b_root_twin_of_pruned_generic_trait_method_fails_closed_too() {
    let v = verdict_at_nth_definition(F16B_TWIN_IN_PRUNED_GENERIC_TRAIT, "f16_dup", 0);
    assert_pruned_identity_refusal("f16b::f16_dup (line lane)", &v);
}

#[test]
fn f16b_distinct_item_controls() {
    assert_verified_then_type_name_refused(
        "f16b",
        F16B_TWIN_IN_PRUNED_GENERIC_TRAIT,
        "f16b_root_le255",
    );
    assert_refuted("f16b", F16B_TWIN_IN_PRUNED_GENERIC_TRAIT, "f16b_root_lt255");
}

/// FAIL-CLOSED (the reviewer's N1, Verified at `66380aa7`): the line-selected
/// twin in the pruned `a::Q` — whose own scope binds u16 — does not borrow the
/// root copy's u8.
#[test]
fn f16c_review_n1_line_selected_twin_fails_closed() {
    let v = verdict_at_nth_definition(F16C_REVIEW_N1_WITH_REFUTING_SCOPE, "n1_dup", 1);
    assert_pruned_identity_refusal("f16c::a::Q::n1_dup (line lane)", &v);
}

/// FAIL-CLOSED, honest incompleteness (as F16a's root copy).
#[test]
fn f16c_review_n1_root_twin_fails_closed_too() {
    let v = verdict_at_nth_definition(F16C_REVIEW_N1_WITH_REFUTING_SCOPE, "n1_dup", 0);
    assert_pruned_identity_refusal("f16c::n1_dup (line lane)", &v);
}

/// FAIL-CLOSED, in the line lane and the bare-name lane: a DISTINCT default
/// method of the pruned `a::Q`. At `c2f6f843` the liar `f16c_q_le255` was
/// refuted and the true `f16c_q_le65535` verified through `a`'s u16 binding,
/// but the same position reads a module const as the root's (F18), so neither
/// is reported now. (`OpaqueTypes` `Unknown` for both at `66380aa7`.)
#[test]
fn f16c_pruned_trait_default_method_is_refused() {
    let src = F16C_REVIEW_N1_WITH_REFUTING_SCOPE;
    for func in ["f16c_q_le255", "f16c_q_le65535"] {
        let line = verdict_at_nth_definition(src, func, 0);
        assert_pruned_identity_refusal(&format!("f16c::a::Q::{func} (line lane)"), &line);
        let bare = verdict("f16c", src, func);
        assert_pruned_identity_refusal(&format!("f16c::a::Q::{func}"), &bare);
    }
}

#[test]
fn f16c_distinct_root_item_controls() {
    let src = F16C_REVIEW_N1_WITH_REFUTING_SCOPE;
    assert_verified_then_type_name_refused("f16c", src, "f16c_root_le255");
    assert_refuted("f16c", src, "f16c_root_lt255");
}

// ---------------------------------------------------------------------------
// F17 — the enclosing-impl `Self` lookup never sees a candidate set the prune
// shrank either.
// ---------------------------------------------------------------------------

/// The extraction-time refusal for a `Self` that token-identical candidates
/// make ambiguous — the fail-closed outcome when the target cannot be pinned to
/// one impl.
fn assert_ambiguous_self_refusal(label: &str, v: &VerifyResult) {
    assert!(
        matches!(
            v,
            VerifyResult::Error { message }
                if message.contains("make `Self` substitution ambiguous")
        ),
        "{label}: expected the ambiguous-`Self` extraction refusal, got {v:?}"
    );
}

/// FAIL-CLOSED (Verified with only the F16 scope change applied): the
/// line-selected default method of the pruned `a::Q` does not borrow `S` as
/// its `Self`.
#[test]
fn f17a_line_selected_trait_default_twin_of_impl_method_fails_closed() {
    let v = verdict_at_nth_definition(F17A_SELF_TWIN_IN_PRUNED_TRAIT, "f17_dup", 1);
    assert_pruned_identity_refusal("f17a::a::Q::f17_dup (line lane)", &v);
}

/// FAIL-CLOSED, honest incompleteness (as F17b): the inherent copy's claim is
/// true, but no identity tells it from its twin in the pruned `a::Q`.
#[test]
fn f17a_impl_twin_of_pruned_trait_default_fails_closed_too() {
    let v = verdict_at_nth_definition(F17A_SELF_TWIN_IN_PRUNED_TRAIT, "f17_dup", 0);
    assert_pruned_identity_refusal("f17a::S::f17_dup (line lane)", &v);
}

/// `Self` substitution and A3 still resolve a distinct inherent method exactly.
#[test]
fn f17a_distinct_item_controls() {
    assert_verified("f17a", F17A_SELF_TWIN_IN_PRUNED_TRAIT, "f17a_s_le255");
    assert_refuted("f17a", F17A_SELF_TWIN_IN_PRUNED_TRAIT, "f17a_s_lt255");
}

/// Parity witness: the unpruned layout refuses both copies the same way.
#[test]
fn f17b_unpruned_trait_twin_refuses_identically() {
    for nth in [0, 1] {
        let v = verdict_at_nth_definition(F17B_SELF_TWIN_IN_UNPRUNED_TRAIT, "f17_dup", nth);
        assert_ambiguous_self_refusal(&format!("f17b::f17_dup #{nth} (line lane)"), &v);
    }
}

// ---------------------------------------------------------------------------
// F18 — a default method of a pruned trait reads its OWN module's consts, so it
// is refused rather than scoped at the crate root (review round 2).
// ---------------------------------------------------------------------------

/// FAIL-CLOSED (review round 2's PZ2: `Err` at `4cd7972e`, `Verified` at
/// `c2f6f843`; in Rust the method returns 9).
#[test]
fn f18a_pruned_default_reading_module_const_is_refused() {
    let v = verdict_at_nth_definition(F18A_PRUNED_DEFAULT_READS_MODULE_CONST, "pz2", 1);
    assert_pruned_identity_refusal("f18a::a::Q::pz2 (line lane)", &v);
}

/// The unrelated same-named impl method is not a copy of the target and still
/// verifies; the root `K` is 7 (a TRUE claim verifies, the liar is refuted), so
/// the pruned method's claim WOULD verify if read in the root's scope.
#[test]
fn f18a_controls() {
    let src = F18A_PRUNED_DEFAULT_READS_MODULE_CONST;
    let impl_method = verdict_at_nth_definition(src, "pz2", 0);
    assert!(
        matches!(impl_method, VerifyResult::Verified),
        "f18a::T::pz2 (line lane): expected Verified, got {impl_method:?}"
    );
    assert_verified("f18a", src, "f18a_root_k_eq7");
    assert_refuted("f18a", src, "f18a_root_k_eq9");
}

/// FAIL-CLOSED (review round 2's PZ3: `Err` at `4cd7972e`, `Verified` at
/// `c2f6f843`; in Rust `pz3(300)` is false).
#[test]
fn f18b_pruned_default_with_projection_and_module_const_is_refused() {
    let v = verdict_at_nth_definition(F18B_PRUNED_DEFAULT_PROJECTION_AND_MODULE_CONST, "pz3", 1);
    assert_pruned_identity_refusal("f18b::a::Q::pz3 (line lane)", &v);
}

#[test]
fn f18b_controls() {
    let src = F18B_PRUNED_DEFAULT_PROJECTION_AND_MODULE_CONST;
    let impl_method = verdict_at_nth_definition(src, "pz3", 0);
    assert!(
        matches!(impl_method, VerifyResult::Verified),
        "f18b::T::pz3 (line lane): expected Verified, got {impl_method:?}"
    );
    assert_verified("f18b", src, "f18b_root_k_or7");
    assert_refuted("f18b", src, "f18b_root_k_ne");
}

/// FAIL-CLOSED (review round 2's PZ2N: `Verified` at `4cd7972e` and at
/// `c2f6f843`), in the line lane and the bare-name lane.
#[test]
fn f18c_pruned_default_without_twin_is_refused() {
    let src = F18C_PRUNED_DEFAULT_NO_TWIN;
    let line = verdict_at_nth_definition(src, "pz2", 0);
    assert_pruned_identity_refusal("f18c::a::Q::pz2 (line lane)", &line);
    assert_pruned_identity_refusal("f18c::a::Q::pz2", &verdict("f18c", src, "pz2"));
}

#[test]
fn f18c_controls() {
    let src = F18C_PRUNED_DEFAULT_NO_TWIN;
    assert_verified("f18c", src, "f18c_root_k_eq7");
    assert_refuted("f18c", src, "f18c_root_k_eq9");
}
