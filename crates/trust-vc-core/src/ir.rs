//! Typed intermediate representation for Rust types in trust_vc.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `TrustVcType` replaces string-based type plumbing throughout the encoder,
//! providing a typed representation of all Rust types understood by trust_vc.
//! Part of #1550 (typed IR epic).

use std::cell::Cell;
use std::collections::BTreeSet;

pub use crate::ir_error::{DatatypeWellFoundednessError, TrustVcTypeParseError};
#[path = "ir_type_parse.rs"]
mod ir_type_parse;

thread_local! {
    /// Per-thread override for the verification target's pointer width, in bits.
    ///
    /// `None` means "use the host platform's `usize::BITS`". A `Some(width)`
    /// value is installed by the `global size_of usize == N` architecture
    /// directive (#2778) and must be one of the widths Rust actually supports
    /// for `usize`/`isize` (16, 32, or 64). The override is thread-local so that
    /// concurrent verification sessions cannot observe each other's target
    /// width, and so that a directive in one source unit never leaks into an
    /// unrelated one. Callers MUST restore the previous value when the
    /// directive's scope ends (see [`PointerWidthGuard`]).
    static POINTER_WIDTH_OVERRIDE: Cell<Option<u32>> = const { Cell::new(None) };
}

/// Returns the pointer width (in bits) for the verification target.
///
/// Defaults to the host platform's pointer width (`usize::BITS`). On 64-bit
/// hosts this is 64; on 32-bit hosts it is 32. When a `global size_of usize ==
/// N` architecture directive (#2778) is in effect on the current thread, that
/// directive's width is returned instead, so that `usize`/`isize` reasoning,
/// shift-overflow bounds, and width-specific bit-vector facts all use the
/// declared target width rather than the host's.
#[must_use]
pub fn pointer_width() -> u32 {
    POINTER_WIDTH_OVERRIDE
        .with(|cell| cell.get())
        .unwrap_or(usize::BITS)
}

/// The widths (in bits) that Rust permits for `usize`/`isize`.
///
/// `global size_of usize == N` declares `size_of::<usize>()` in *bytes*, so the
/// accepted byte values are `{2, 4, 8}` mapping to `{16, 32, 64}` bits. Other
/// widths are rejected rather than silently accepted, because admitting a width
/// Rust never uses would let a proof "succeed" against an unrealizable target
/// (a soundness hazard).
const SUPPORTED_USIZE_WIDTHS: [u32; 3] = [16, 32, 64];

/// Installs a target pointer width for the current thread, restoring the
/// previous value when dropped.
///
/// This RAII guard is the only supported way to scope a `global size_of usize`
/// override: it guarantees the override never outlives the verification of the
/// source unit that declared it, even on early return or panic. Nesting is
/// supported — the guard restores whatever value was in effect when it was
/// created, not unconditionally `None`.
#[must_use = "the override is reverted when the guard is dropped; bind it to a name"]
pub struct PointerWidthGuard {
    previous: Option<u32>,
}

impl PointerWidthGuard {
    /// Installs `width_bits` as the current thread's pointer width.
    ///
    /// `width_bits` MUST be one of `SUPPORTED_USIZE_WIDTHS`; callers should
    /// validate via [`parse_global_size_of_usize`] before constructing the
    /// guard. Construction does not itself reject unsupported widths because
    /// the supported set is enforced at the directive-parsing boundary; this
    /// keeps the guard a thin, infallible scope mechanism.
    pub fn install(width_bits: u32) -> Self {
        let previous = POINTER_WIDTH_OVERRIDE.with(|cell| cell.replace(Some(width_bits)));
        Self { previous }
    }
}

impl Drop for PointerWidthGuard {
    fn drop(&mut self) {
        POINTER_WIDTH_OVERRIDE.with(|cell| cell.set(self.previous));
    }
}

/// Reads the pinned target width out of a [`scan_pointer_width_directive`] result,
/// then releases the guard so the caller starts from a clean (override-free) state.
///
/// A scanned guard has already *installed* its declared width as the current
/// thread's override. This helper observes that width via [`pointer_width`] and
/// then drops the guard, restoring whatever was in effect before the scan. It is
/// used by callers that re-derive and re-install the width themselves per
/// verification pass (e.g. the dual-arch usize encoding, #2778), where holding the
/// scanned guard for the whole function would conflict with the per-pass guards.
///
/// Returns `Some(width_bits)` when a directive was present (`guard.is_some()`),
/// `None` otherwise.
#[must_use]
pub fn pinned_width_from_guard(guard: Option<PointerWidthGuard>) -> Option<u32> {
    guard.map(|guard| {
        let width = pointer_width();
        drop(guard);
        width
    })
}

/// Parses a `global size_of usize == N;` architecture directive (#2778).
///
/// Accepts the exact Verus surface syntax `global size_of usize == N` (an
/// optional trailing `;` and surrounding whitespace are tolerated), where `N`
/// is the size of `usize` in **bytes**. Returns the corresponding pointer
/// **width in bits** on success.
///
/// Returns `None` when the line is not this directive at all (so callers can
/// keep scanning), and `Err`-like `None` is *not* used for malformed widths:
/// a recognized `global size_of usize == N` with an unsupported `N` returns
/// `Some(Err(..))`, distinguishing "not this directive" from "this directive,
/// but with an illegal width". Illegal widths must fail closed rather than be
/// silently ignored — accepting them would verify against a target Rust cannot
/// produce.
#[must_use]
pub fn parse_global_size_of_usize(line: &str) -> Option<Result<u32, String>> {
    let line = line.trim().trim_end_matches(';').trim();
    let rest = line.strip_prefix("global")?;
    // Require whitespace after `global` so we don't match `globalsize_of...`.
    if !rest.starts_with(char::is_whitespace) {
        return None;
    }
    let rest = rest.trim_start();
    let rest = rest.strip_prefix("size_of")?;
    if !rest.starts_with(char::is_whitespace) {
        return None;
    }
    let rest = rest.trim_start();
    let rest = rest.strip_prefix("usize")?;
    // `usize` must be a standalone token, not a prefix of e.g. `usize_t`.
    if rest
        .chars()
        .next()
        .is_some_and(|c| c.is_alphanumeric() || c == '_')
    {
        return None;
    }
    let rest = rest.trim_start();
    let rest = rest.strip_prefix("==")?;
    let bytes_str = rest.trim();
    let bytes: u32 = match bytes_str.parse() {
        Ok(n) => n,
        Err(_) => {
            return Some(Err(format!(
                "global size_of usize: expected a byte count, found `{bytes_str}`"
            )));
        }
    };
    // Guard against `bytes * 8` overflowing u32 for absurd inputs before the
    // width check rejects them anyway.
    let width_bits = bytes
        .checked_mul(8)
        .filter(|w| SUPPORTED_USIZE_WIDTHS.contains(w));
    match width_bits {
        Some(width) => Some(Ok(width)),
        None => Some(Err(format!(
            "global size_of usize == {bytes}: unsupported usize size; \
             Rust supports usize widths of {} bits (sizes 2, 4, or 8 bytes)",
            SUPPORTED_USIZE_WIDTHS
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        ))),
    }
}

/// Scans a source/spec text for a `global size_of usize == N;` directive and,
/// if present, returns a [`PointerWidthGuard`] installing the declared width
/// for the current thread.
///
/// Returns:
/// - `Ok(None)` when no directive is present (host width stays in effect).
/// - `Ok(Some(guard))` when a valid directive is found; the caller MUST hold
///   the guard for the duration of verification.
/// - `Err(msg)` when a `global size_of usize` directive is present but declares
///   an unsupported width — this fails closed rather than verifying against an
///   unrealizable target.
///
/// Multiple conflicting directives in the same text are an error: a target with
/// two different pointer widths is contradictory, and silently picking one
/// could mask a real mistake.
pub fn scan_pointer_width_directive(source: &str) -> Result<Option<PointerWidthGuard>, String> {
    let mut found: Option<u32> = None;
    for line in source.lines() {
        match parse_global_size_of_usize(line) {
            None => {}
            Some(Err(msg)) => return Err(msg),
            Some(Ok(width)) => match found {
                None => found = Some(width),
                Some(prev) if prev == width => {}
                Some(prev) => {
                    return Err(format!(
                        "conflicting `global size_of usize` directives: {} bits vs {} bits",
                        prev, width
                    ));
                }
            },
        }
    }
    Ok(found.map(PointerWidthGuard::install))
}

/// Removes `global size_of usize == N;` directive lines from a source unit,
/// replacing each with an empty line so byte/line offsets of the surviving Rust
/// code are preserved for diagnostics.
///
/// The directive is a unit-level *pragma* (Verus surface syntax), not a Rust
/// item: it configures the verification target's pointer width and is consumed
/// by [`scan_pointer_width_directive`]. It is not valid Rust at item position,
/// so it must be stripped before the unit is handed to the parser. Lines that
/// are *malformed* directives (e.g. an unsupported width) are left untouched
/// here; `scan_pointer_width_directive` is responsible for failing closed on
/// those, and stripping them would mask the error.
#[must_use]
pub fn strip_pointer_width_directives(source: &str) -> String {
    // Fast path: if no line is a *valid* directive, return the source verbatim.
    // This keeps the common (directive-free) case byte-for-byte identical —
    // including line endings — so the parser sees exactly the original unit.
    if !source
        .lines()
        .any(|line| matches!(parse_global_size_of_usize(line), Some(Ok(_))))
    {
        return source.to_owned();
    }
    let mut out = String::with_capacity(source.len());
    let mut first = true;
    for line in source.lines() {
        if !first {
            out.push('\n');
        }
        first = false;
        // Only blank out lines that parse as a *valid* directive; malformed
        // ones (`Some(Err(..))`) stay so the scanner can report them.
        if !matches!(parse_global_size_of_usize(line), Some(Ok(_))) {
            out.push_str(line);
        }
    }
    // Preserve a trailing newline if the original had one (lines() drops it).
    if source.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// Conservatively decides whether verifying `func` depends on the target pointer
/// width, i.e. whether the proof could differ between a 32-bit and a 64-bit
/// `usize`/`isize` (#2778 dual-arch).
///
/// SOUNDNESS DIRECTION. Over-approximating is sound: a width-invariant unit
/// simply verifies identically at both widths, at the cost of one extra solver
/// pass. Under-approximating is UNSOUND — a genuinely width-dependent proof
/// would be discharged at only one width, so a program that is FALSE at a 32-bit
/// `usize` comes back `verified` on a 64-bit host. This function must therefore
/// err toward inclusion, and every judgement below is written in that direction.
///
/// WHY THE UNIT'S OWN TOKENS ARE NOT ENOUGH (the FV-2 hole). The predicate used
/// to scan only `func.to_token_stream()`. `usize` reaches a unit through routes
/// that put no `usize` token inside the function:
///
/// * a type alias — `type Idx = usize; fn f(x: Idx) -> Idx`;
/// * a NESTED alias — `type Idx2 = Idx;`;
/// * a struct FIELD — `struct H { n: usize } fn f(h: H)`;
/// * a definition in a sibling module the caller merged into the file AST.
///
/// The rest of the pipeline resolves all of these correctly (pinning
/// `global size_of usize == 4` refutes every one of them), so only the plan
/// selector was blind — the worst possible place for the blindness, because it
/// decides whether the refuting pass runs at all. The scan therefore covers the
/// WHOLE FILE the unit lives in, not just the unit: any `usize`/`isize` reachable
/// through a file-local (or caller-merged) definition is a token SOMEWHERE in
/// that file.
///
/// A file the caller could not fully materialise is treated as width-dependent:
/// an out-of-line `mod m;` and a crate-local `use crate::`/`use super::`/`use
/// self::` import both name definitions that are not in `file`'s tokens, so we
/// cannot rule out a `usize` behind them. `use` of an EXTERNAL crate is not
/// included — those items are not resolved into the type environment at all and
/// fail closed on their own.
///
/// Numeric literal suffixes (`4294967295usize`) are part of a `Literal` token,
/// not a separate `Ident`; missing them verified suffix-only pointer-width
/// arithmetic at the host width alone. String literals keep their closing quote
/// in this representation, so they cannot match these suffixes.
///
/// Callers pass `None` for `file` only when no file AST exists; that degrades to
/// the unit-local scan and is strictly weaker — prefer passing the AST.
#[must_use]
pub fn unit_is_pointer_width_polymorphic(file: Option<&syn::File>, func: &syn::ItemFn) -> bool {
    use quote::ToTokens;

    if tokens_mention_pointer_width(func.to_token_stream()) {
        return true;
    }
    let Some(file) = file else {
        return false;
    };
    file_is_pointer_width_polymorphic(file)
}

/// The FILE half of [`unit_is_pointer_width_polymorphic`], for obligations that
/// belong to the FILE rather than to any one function.
///
/// A trait-impl CONFORMANCE obligation is an obligation of the IMPL: there is no
/// "current function" to hand over (the impl body lives in an `Item::Impl`, not
/// an `ItemFn`), and the obligation is checked whether or not any function in
/// the file calls it. So the conformance lane needs the file scan on its own.
///
/// This is deliberately the SAME body [`unit_is_pointer_width_polymorphic`]
/// runs, not a sibling copy: the unit predicate already existed twice (here and
/// hand-copied into `cargo-trust-vc`'s `verify.rs`) and the copies drifted into
/// a false verify. One body, two entry points.
#[must_use]
pub(crate) fn file_is_pointer_width_polymorphic(file: &syn::File) -> bool {
    use quote::ToTokens;

    file.items.iter().any(|item| {
        item_hides_definitions(item) || tokens_mention_pointer_width(item.to_token_stream())
    })
}

/// True when `item` brings names into scope whose definitions are NOT part of
/// this file's token stream, so a `usize` could hide behind them.
fn item_hides_definitions(item: &syn::Item) -> bool {
    match item {
        // `mod m;` — the module body lives in another file we did not parse.
        // `mod m { .. }` is inline and IS covered by the token scan.
        syn::Item::Mod(module) => module.content.is_none(),
        // Crate-local imports are resolved into the type/spec environment by the
        // catalog, but their definitions are not in this file's tokens.
        syn::Item::Use(use_item) => use_tree_is_crate_local(&use_item.tree),
        _ => false,
    }
}

/// True for a `use` whose first path segment is `crate` / `super` / `self`.
fn use_tree_is_crate_local(tree: &syn::UseTree) -> bool {
    match tree {
        syn::UseTree::Path(path) => {
            let root = path.ident.to_string();
            root == "crate" || root == "super" || root == "self"
        }
        syn::UseTree::Name(name) => {
            let root = name.ident.to_string();
            root == "crate" || root == "super" || root == "self"
        }
        syn::UseTree::Group(group) => group.items.iter().any(use_tree_is_crate_local),
        // `use ::*` is not expressible; a rename/glob at the root has no path
        // prefix to classify, so it names no crate-local module.
        syn::UseTree::Rename(_) | syn::UseTree::Glob(_) => false,
    }
}

/// Recursively scans a token stream for a `usize`/`isize` ident or numeric
/// literal suffix.
fn tokens_mention_pointer_width(tokens: proc_macro2::TokenStream) -> bool {
    use proc_macro2::TokenTree;
    for tree in tokens {
        match tree {
            TokenTree::Ident(ident) => {
                let name = ident.to_string();
                if name == "usize" || name == "isize" {
                    return true;
                }
            }
            TokenTree::Literal(literal) => {
                let text = literal.to_string();
                if text.ends_with("usize") || text.ends_with("isize") {
                    return true;
                }
            }
            TokenTree::Group(group) if tokens_mention_pointer_width(group.stream()) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

// Phase 3 compatibility surface: expression IR is currently defined in
// `ir_expr.rs` but exported here to keep typed IR consumers on `crate::ir::*`.
pub use crate::ir_expr::{
    ArithOp, CollectionOp, CompareOp, IntConstKind, LogicOp, MatchArm, MatchPattern,
    QuantifierKind, SpecialArithOp, StructPatternField, TrustVcExpr, WrappingMode,
};
// Place IR for memory location reasoning (#2515) is in `ir_place.rs`.

/// A single variant of an algebraic datatype with named fields.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct DatatypeVariant {
    pub name: String,
    pub fields: Vec<(String, TrustVcType)>,
}

impl DatatypeVariant {
    /// Creates datatype metadata for a single variant.
    #[must_use]
    pub fn new(name: impl Into<String>, fields: Vec<(String, TrustVcType)>) -> Self {
        Self {
            name: name.into(),
            fields,
        }
    }
}

/// Named-field struct definition for struct invariant verification (#2419).
///
/// Converts to `TrustVcType::Datatype` with a single variant whose name
/// matches the struct name. This mirrors how Verus encodes struct types.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<(String, TrustVcType)>,
    /// Whether the source `struct`/`enum` carried `#[derive(PartialEq)]` — its
    /// `==`/`.eq()` is then the STRUCTURAL field-wise equality (no custom impl).
    pub derived_partial_eq: bool,
    /// Whether the source carried `#[derive(Clone)]` — `.clone()` is then the
    /// structural value copy.
    pub derived_clone: bool,
}

impl StructDef {
    /// Creates a new struct definition (no derives recorded).
    #[must_use]
    pub fn new(name: impl Into<String>, fields: Vec<(String, TrustVcType)>) -> Self {
        Self {
            name: name.into(),
            fields,
            derived_partial_eq: false,
            derived_clone: false,
        }
    }

    /// Records the `#[derive(PartialEq)]` / `#[derive(Clone)]` presence.
    #[must_use]
    pub fn with_derives(mut self, derived_partial_eq: bool, derived_clone: bool) -> Self {
        self.derived_partial_eq = derived_partial_eq;
        self.derived_clone = derived_clone;
        self
    }

    /// Converts to a `TrustVcType::Datatype` with a single variant.
    #[must_use]
    pub fn to_datatype_type(&self) -> TrustVcType {
        TrustVcType::Datatype {
            name: self.name.clone(),
            variants: vec![DatatypeVariant::new(self.name.clone(), self.fields.clone())],
        }
    }
}

/// Declaration of a trait's verification-relevant surface.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct TraitDecl {
    pub name: String,
    pub methods: Vec<TraitMethodDecl>,
    /// Names of the trait's direct supertraits (`trait T: Super`). Used to form
    /// the supertrait-method closure for caller-side `requires` discharge (unit
    /// 6): a method declared on `Super` is still callable through a `T`-bounded
    /// or `impl T for S` receiver, so `Super`'s requires must be discharged at
    /// the call site. Empty when the trait has no supertrait bounds.
    pub supertraits: Vec<String>,
    /// Ordered declaration-order type-parameter names of a parameterized trait
    /// (`trait T<A, B>` → `["A", "B"]`). Empty for a non-generic trait. The
    /// order is load-bearing: instantiation zips these against an impl's
    /// `trait_type_args` positionally.
    pub generics: Vec<String>,
}

impl TraitDecl {
    /// Creates a trait declaration with the given name and method signatures.
    ///
    /// Supertraits default to empty; use [`TraitDecl::with_supertraits`] to set
    /// them, keeping this two-argument constructor stable for existing callers.
    #[must_use]
    pub fn new(name: impl Into<String>, methods: Vec<TraitMethodDecl>) -> Self {
        Self {
            name: name.into(),
            methods,
            supertraits: Vec::new(),
            generics: Vec::new(),
        }
    }

    /// Sets the trait's direct supertrait names (builder style).
    #[must_use]
    pub fn with_supertraits(mut self, supertraits: Vec<String>) -> Self {
        self.supertraits = supertraits;
        self
    }

    /// Sets the trait's ordered type-parameter names (builder style).
    #[must_use]
    pub fn with_generics(mut self, generics: Vec<String>) -> Self {
        self.generics = generics;
        self
    }
}

/// A single trait method declaration with its contract.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct TraitMethodDecl {
    pub name: String,
    pub params: Vec<(String, TrustVcType)>,
    pub return_type: TrustVcType,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
    pub has_default: bool,
    /// The default body expression as a string, if this method has a default
    /// implementation. Used to generate body axioms for inherited defaults.
    pub default_body: Option<String>,
    /// Extra postconditions the trait DEFAULT BODY must establish; checked at
    /// the decl site. NOT yet published to callers.
    pub default_ensures: Vec<String>,
}

impl TraitMethodDecl {
    /// Creates a trait method declaration with its signature and contract.
    #[must_use]
    pub fn new(
        name: impl Into<String>,
        params: Vec<(String, TrustVcType)>,
        return_type: TrustVcType,
        requires: Vec<String>,
        ensures: Vec<String>,
        has_default: bool,
        default_body: Option<String>,
    ) -> Self {
        Self {
            name: name.into(),
            params,
            return_type,
            requires,
            ensures,
            has_default,
            default_body,
            default_ensures: Vec::new(),
        }
    }

    /// Sets the extra postconditions the trait DEFAULT BODY must establish
    /// (builder style). These are checked at the decl site by the
    /// default-body conformance pass and are NOT published to callers in this
    /// increment.
    #[must_use]
    pub fn with_default_ensures(mut self, default_ensures: Vec<String>) -> Self {
        self.default_ensures = default_ensures;
        self
    }
}

/// Registration of an impl block for trait verification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct TraitImplDecl {
    pub trait_name: String,
    pub concrete_type: TrustVcType,
    pub method_bindings: Vec<(String, String)>,
    /// Associated-type bindings declared by the impl (`type X = T;`), used to
    /// normalize `Self::X` projections in trait method signatures before the
    /// impl's methods are registered or conformance-checked. Without this, a
    /// trait method param typed `Self::X` reaches registration as
    /// `Opaque("Self::X")` and fails the whole file closed even though the
    /// impl binds `X` to a fully concrete type.
    pub assoc_type_bindings: Vec<(String, TrustVcType)>,
    /// `#[trust_vc::external]` on the impl: the Verus
    /// `external_trait_specification` trust model. The impl's method BODIES are
    /// trusted, not verified — the trait contract is assumed to hold for this
    /// impl, so the trait-impl body-conformance pass must skip it (its written
    /// body may legitimately diverge from what the spec describes, e.g. FFI or
    /// deliberately-unmodeled code). Callers still consume the trait contract.
    /// Non-external impls keep full fail-closed conformance checking.
    pub is_external: bool,
    /// Ordered type arguments of the trait path in the impl header
    /// (`impl T<u64> for S` → `[Uint{64}]`). Empty when the impl writes no
    /// angle-bracketed args. Zipped positionally against `TraitDecl::generics`
    /// to instantiate bare-TypeParam method-signature positions; a
    /// non-concrete entry (TypeParam-bearing or Opaque) makes every generic
    /// method of the impl non-instantiable, fail-closed.
    pub trait_type_args: Vec<TrustVcType>,
    /// TRAIT-method names whose shared concrete symbol `Type__method` this impl
    /// may NOT claim, because the source file resolves that symbol to some
    /// OTHER declaration — an inherent `impl Type { fn method }` (Rust's
    /// shadowing rule) or a second trait impl of the same name (unresolvable).
    ///
    /// SOUNDNESS-CRITICAL. `method_bindings` maps a trait method to
    /// `format!("{type}__{method}")`, which carries the self type but NOT the
    /// trait, so it is not an identity: an inherent `T::w` and `impl B1 for T`
    /// mint the SAME string. The per-impl linking axiom
    /// `B1__w(Box_T(t)) == T__w(t)` then equates the trait UF with a symbol the
    /// inherent method also defines. With the inherent body axiom present
    /// (`T__w(t) == 4`) and the trait postcondition axiom present
    /// (`B1__w(_) == 9`), the context asserts `4 == 9` — a CONTRADICTION, which
    /// proves every claim in the file. With the inherent body axiom suppressed
    /// instead, the trait's `ensures` silently answers the INHERENT call site:
    /// measured as a cardinal false verify where `ensures(result == 9)` over
    /// `t.w()` VERIFIED while the true `result == 4` was refuted.
    ///
    /// Populated by the file lane, which is the only lane that can see the
    /// competing declarations; empty elsewhere, which is exactly today's
    /// behaviour for a single-item expansion.
    pub inherent_shadowed_methods: std::collections::BTreeSet<String>,
}

impl TraitImplDecl {
    /// Creates a trait impl registration binding methods to a concrete type.
    #[must_use]
    pub fn new(
        trait_name: impl Into<String>,
        concrete_type: TrustVcType,
        method_bindings: Vec<(String, String)>,
    ) -> Self {
        Self {
            trait_name: trait_name.into(),
            concrete_type,
            method_bindings,
            assoc_type_bindings: Vec::new(),
            is_external: false,
            trait_type_args: Vec::new(),
            inherent_shadowed_methods: std::collections::BTreeSet::new(),
        }
    }

    /// Records the trait-method names whose shared concrete symbol this impl may
    /// not claim (see [`Self::inherent_shadowed_methods`]).
    #[must_use]
    pub fn with_inherent_shadowed_methods(
        mut self,
        shadowed: std::collections::BTreeSet<String>,
    ) -> Self {
        self.inherent_shadowed_methods = shadowed;
        self
    }

    /// Equality on every field EXCEPT [`Self::inherent_shadowed_methods`].
    ///
    /// Used by `VerificationContext::register_trait_impl` to recognise that two
    /// producers described the SAME impl and merge their shadow sets, rather
    /// than storing both and letting the unshadowed copy re-publish the axioms
    /// the shadowed copy withheld. Written as an exhaustive destructure so that
    /// a field added later must be classified deliberately — either it
    /// distinguishes two impls (compare it) or it is merged metadata like the
    /// shadow set (union it) — instead of being silently ignored.
    #[must_use]
    pub fn matches_ignoring_shadowed_methods(&self, other: &Self) -> bool {
        let Self {
            trait_name,
            concrete_type,
            method_bindings,
            assoc_type_bindings,
            is_external,
            trait_type_args,
            inherent_shadowed_methods: _,
        } = self;
        *trait_name == other.trait_name
            && *concrete_type == other.concrete_type
            && *method_bindings == other.method_bindings
            && *assoc_type_bindings == other.assoc_type_bindings
            && *is_external == other.is_external
            && *trait_type_args == other.trait_type_args
    }

    /// Whether this impl may publish a contract about the shared concrete
    /// symbol `Type__method` for `trait_method_name`. `false` means the file
    /// resolves that symbol to a different declaration, so the impl must
    /// publish NOTHING about it — the linking axiom and the concrete-sorted
    /// trait-ensures axiom both consult this.
    #[must_use]
    pub fn may_claim_concrete_symbol(&self, trait_method_name: &str) -> bool {
        !self.inherent_shadowed_methods.contains(trait_method_name)
    }

    /// Attaches the ordered trait-path type arguments (`impl T<u64> for S`).
    #[must_use]
    pub fn with_trait_type_args(mut self, trait_type_args: Vec<TrustVcType>) -> Self {
        self.trait_type_args = trait_type_args;
        self
    }

    /// Attaches associated-type bindings (`type X = T;`) declared by the impl.
    #[must_use]
    pub fn with_assoc_type_bindings(mut self, bindings: Vec<(String, TrustVcType)>) -> Self {
        self.assoc_type_bindings = bindings;
        self
    }

    /// Marks the impl `#[trust_vc::external]` (trusted bodies, skipped by the
    /// trait-impl body-conformance pass; Verus `external_trait_specification`).
    #[must_use]
    pub fn with_external(mut self, is_external: bool) -> Self {
        self.is_external = is_external;
        self
    }

    /// Rewrites associated-type projections in `ty` to the impl's bound type,
    /// recursing through container types. Both the trait-signature spelling
    /// `Self::X` and the fully-qualified spelling `<Concrete as Trait>::X` are
    /// resolved (see `Self::resolve_projection_name`). Projections without a
    /// binding (or bindings that are themselves unresolvable) are left as-is,
    /// so every existing `contains_opaque()` fail-closed guard still rejects
    /// them — this only *resolves*, it never invents a type.
    #[must_use]
    pub fn resolve_assoc_projections(&self, ty: &TrustVcType) -> TrustVcType {
        if self.assoc_type_bindings.is_empty() {
            return ty.clone();
        }
        match ty {
            TrustVcType::Opaque(name) => self
                .resolve_projection_name(name)
                .cloned()
                .unwrap_or_else(|| ty.clone()),
            TrustVcType::Seq(inner) => {
                TrustVcType::Seq(Box::new(self.resolve_assoc_projections(inner)))
            }
            TrustVcType::Array(inner, len) => {
                TrustVcType::Array(Box::new(self.resolve_assoc_projections(inner)), *len)
            }
            TrustVcType::Set(inner) => {
                TrustVcType::Set(Box::new(self.resolve_assoc_projections(inner)))
            }
            TrustVcType::Multiset(inner) => {
                TrustVcType::Multiset(Box::new(self.resolve_assoc_projections(inner)))
            }
            TrustVcType::Map(key, value) => TrustVcType::Map(
                Box::new(self.resolve_assoc_projections(key)),
                Box::new(self.resolve_assoc_projections(value)),
            ),
            TrustVcType::SpecFn(args, ret) => TrustVcType::SpecFn(
                args.iter()
                    .map(|arg| self.resolve_assoc_projections(arg))
                    .collect(),
                Box::new(self.resolve_assoc_projections(ret)),
            ),
            TrustVcType::Datatype { name, variants } => TrustVcType::Datatype {
                name: name.clone(),
                variants: variants
                    .iter()
                    .map(|variant| DatatypeVariant {
                        name: variant.name.clone(),
                        fields: variant
                            .fields
                            .iter()
                            .map(|(field_name, field_ty)| {
                                (field_name.clone(), self.resolve_assoc_projections(field_ty))
                            })
                            .collect(),
                    })
                    .collect(),
            },
            other => other.clone(),
        }
    }

    /// Resolves an associated-type projection SPELLING to this impl's bound
    /// type, or `None` when it names no assoc this impl binds.
    ///
    /// Accepts the trait-signature form `Self::X` and the fully-qualified form
    /// `<Concrete as Trait>::X`. The qualified form resolves ONLY when it names
    /// THIS impl's own concrete type and trait — i.e. it is exactly
    /// `<Self as ThisTrait>::X`, so it resolves identically to `Self::X` and
    /// inherits the same (sound) sort. A qualified projection naming a DIFFERENT
    /// type or trait is left unresolved (fail-closed): the per-trait UF encoding
    /// fixes an assoc slot's sort from the DECLARED type, so resolving a foreign
    /// projection at this seam could sort-diverge from that slot. Concrete
    /// resolution of a foreign projection is performed structurally, pre-parse,
    /// at the target-lifting seam (`AssocProjectionResolver`), where it lands in
    /// a fresh variable's own sort rather than a shared per-trait UF slot.
    fn resolve_projection_name(&self, name: &str) -> Option<&TrustVcType> {
        let assoc: &str = if let Some(assoc) = name.strip_prefix("Self::") {
            assoc
        } else {
            let (concrete, trait_name, assoc) = parse_qualified_projection(name)?;
            if concrete != self.concrete_type.to_type_string() || trait_name != self.trait_name {
                return None;
            }
            assoc
        };
        self.assoc_type_bindings
            .iter()
            .find(|(assoc_name, _)| assoc_name == assoc)
            .map(|(_, bound)| bound)
    }
}

/// Parses a fully-qualified associated-type projection spelling
/// `<Concrete as Trait>::Assoc` into its three components (whitespace-tolerant),
/// or `None` for any other shape. Only the canonical single-spaced `as` form is
/// recognized; a projection whose `as` word boundary was collapsed by token
/// re-rendering is left unrecognized (it fails closed, or is resolved earlier at
/// the structural syn seam).
fn parse_qualified_projection(name: &str) -> Option<(&str, &str, &str)> {
    let inner = name.trim().strip_prefix('<')?;
    let (qualified, assoc) = inner.split_once(">::")?;
    let (concrete, trait_name) = qualified.split_once(" as ")?;
    let concrete = concrete.trim();
    let trait_name = trait_name.trim();
    let assoc = assoc.trim();
    (!concrete.is_empty() && !trait_name.is_empty() && !assoc.is_empty())
        .then_some((concrete, trait_name, assoc))
}

/// A trait-impl method body captured for auxiliary conformance verification.
///
/// `body_text` is the impl method's single pure return expression with the
/// receiver written as `self` and the i-th non-receiver parameter renamed to the
/// positional canonical name `__trust_vc_conf_arg_{i}`. The conformance pass
/// re-binds these onto its `__trust_vc_impl_*` surface positionally to assume the
/// definitional `concrete_fn(self, args..) == body` fact, so the trait contract
/// is checked against what the impl body ACTUALLY returns rather than an
/// unconstrained `concrete_fn(..)` UF (which over-rejects when the verified
/// function does not itself reference the impl method, leaving no body axiom in
/// scope). Captured ONLY for bodies that pass the single-pure-return soundness
/// gate (no `requires`, no parameter shadowing, single return expression); absent
/// otherwise, in which case the conformance check keeps its prior body-axiom
/// path. The captured text being the method's true return value is the soundness
/// linchpin: a wrong body would assume a false definitional fact.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConformanceMethodBody {
    pub body_text: String,
    pub param_count: usize,
}

impl ConformanceMethodBody {
    /// Creates a captured conformance body from its canonicalized return-value
    /// text and non-receiver parameter count.
    #[must_use]
    pub fn new(body_text: impl Into<String>, param_count: usize) -> Self {
        Self {
            body_text: body_text.into(),
            param_count,
        }
    }
}

/// Identity of one TRAIT-IMPL method, for the maps the conformance lane keys.
///
/// The concrete UF name alone (`format!("{type}__{method}")`, produced by
/// `parse_trait_impl_decl`) is NOT an identity: it carries the self type but not
/// the trait, so `impl A1 for S` and `impl A2 for S` both mint `S__v`. The maps
/// keyed by that string are first-registration-wins, and their doc comments used
/// to assert "unique per concrete name" — which THREE traits for one type
/// falsify. Measured through the production CLI, cache off, with `A1/A2/A3`
/// each declaring `fn v(&self) -> u64` for one struct `S` returning `1/2/3`:
///
/// ```text
/// trait impl conformance A1::v for S -> verified
/// trait impl conformance A2::v for S -> counterexample   (model: result = 1)
/// trait impl conformance A3::v for S -> counterexample   (model: result = 1)
/// ```
///
/// The counterexample model naming `1` is the proof of misattribution: A1's
/// captured body answered A2's and A3's conformance obligations. Fail-closed in
/// direction, but it makes multi-trait code unverifiable.
///
/// Carrying the trait makes the collision unrepresentable rather than merely
/// detected. There is deliberately no `Default` and no field-by-field literal
/// constructor: [`Self::new`] is the only way to build one, so a caller cannot
/// forget the trait and silently re-create the trait-erased key.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ImplMethodKey {
    trait_name: String,
    concrete_fn: String,
}

impl ImplMethodKey {
    /// Keys a trait-impl method by its declaring TRAIT and its concrete UF name.
    #[must_use]
    pub fn new(trait_name: impl Into<String>, concrete_fn: impl Into<String>) -> Self {
        Self {
            trait_name: trait_name.into(),
            concrete_fn: concrete_fn.into(),
        }
    }

    /// The declaring trait's name.
    #[must_use]
    pub fn trait_name(&self) -> &str {
        &self.trait_name
    }

    /// The concrete UF name (`Type__method`) this method encodes to. NOT unique
    /// on its own — see the type's doc comment.
    #[must_use]
    pub fn concrete_fn(&self) -> &str {
        &self.concrete_fn
    }

    /// A stable, collision-free rendering for cache keys and diagnostics.
    #[must_use]
    pub fn canonical_string(&self) -> String {
        format!("{}::{}", self.trait_name, self.concrete_fn)
    }
}

/// A trait bound on a type parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct TraitBound {
    pub type_param: String,
    pub trait_name: String,
}

impl TraitBound {
    /// Creates a trait bound constraining `type_param` to implement `trait_name`.
    #[must_use]
    pub fn new(type_param: impl Into<String>, trait_name: impl Into<String>) -> Self {
        Self {
            type_param: type_param.into(),
            trait_name: trait_name.into(),
        }
    }
}

/// Typed representation of all Rust types understood by trust_vc.
///
/// Replaces string-based type plumbing (`&str` type names) with a proper enum.
/// Used throughout lowering and verification setup without committing the IR
/// layer to a specific solver backend.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TrustVcType {
    /// Rust unit type `()`; exactly one value, the unit literal `()`.
    Unit,
    /// Rust `bool` -> ay `Bool`
    Bool,
    /// Signed integers: i8/i16/i32/i64/i128/isize -> ay `BitVec(width)`
    Int { width: u32 },
    /// Unsigned integers: u8/u16/u32/u64/u128/usize -> ay `BitVec(width)`
    Uint { width: u32 },
    /// Unbounded mathematical integer for termination proofs -> ay `Int`
    MathInt,
    /// Non-negative unbounded integer (Verus `nat`) -> ay `Int` with >= 0 guard.
    /// Behaves identically to `MathInt` in the solver backend except that the
    /// encoder emits an assumption `x >= 0` for every Nat-typed variable.
    Nat,
    /// Spec-level mathematical real number (Verus `Real`) -> ay `Real`.
    /// Used for exact real arithmetic in specifications. Not IEEE 754.
    Real,
    /// IEEE 754 float: f32/f64. Kept separate from `Real` so spec-level real
    /// arithmetic stays distinct from native SMT floating-point semantics.
    Float { width: u32 },
    /// Rust `char` -> ay `BitVec(32)` with Unicode scalar-value guards.
    Char,
    /// Rust `str` runtime surface -> same backend shape as `Seq<char>`.
    StrSlice,
    /// Rust `String` runtime surface -> same backend shape as `Seq<char>`.
    String,
    /// Spec-only sequence: `Seq<T>` -> ay `Array(BitVec(pointer_width()), T)`
    Seq(Box<TrustVcType>),
    /// Rust fixed-size array `[T; N]`, encoded with Seq-like element storage and
    /// a fixed length companion.
    Array(Box<TrustVcType>, usize),
    /// Spec-only set: `Set<T>` -> ay `Array(T, Bool)`
    Set(Box<TrustVcType>),
    /// Spec-only multiset/bag: `Multiset<T>` -> ay `Array(T, Int)`
    Multiset(Box<TrustVcType>),
    /// Spec-only map: `Map<K,V>` -> ay `Array(K, V)`
    Map(Box<TrustVcType>, Box<TrustVcType>),
    /// Spec-only closure value used by higher-order collection combinators.
    ///
    /// The first field stores the flattened argument types. A unary spec
    /// function such as `SpecFn<i32, bool>` stores one argument type; a tupled
    /// closure type such as `SpecFn<(usize, i32), bool>` stores two.
    SpecFn(Vec<TrustVcType>, Box<TrustVcType>),
    /// Built-in algebraic datatypes such as `Option<T>` and `Result<T, E>`.
    ///
    /// The encoder's datatype UF layer uses the variant metadata to declare
    /// constructors, selectors, and testers, while `name` preserves the
    /// canonical Rust-style surface string for round-tripping and diagnostics.
    Datatype {
        name: String,
        variants: Vec<DatatypeVariant>,
    },
    /// Reference to a recursive datatype carrier without inlining its variants.
    /// Encodes to the datatype carrier sort (`Sort::Int`) in the UF backend.
    RecursiveRef(String),
    /// Generic type parameter from function signature (e.g., `T`, `U`).
    /// The string is the parameter name as written in the source.
    /// Encoded as `Sort::Uninterpreted("Poly")` at the SMT level.
    /// Part of #2053 (polymorphism encoding).
    TypeParam(String),

    /// The universal erased sort for polymorphic encoding.
    /// Variables of type `Poly` are used inside generic function bodies.
    /// Only appears in encoder-generated code, never in user-written specs.
    /// Part of #2053 (polymorphism encoding).
    Poly,

    /// Unrecognized type from runtime type inference (e.g., `Widget`).
    /// Retained for lossy parsing compatibility, but `verify_typed()` rejects
    /// contexts with Opaque-typed variables (including nested, e.g.
    /// `Seq<Widget>`) via `contains_opaque()` before encoding to prevent
    /// spurious proofs (#1926). Preserves the original type name for
    /// diagnostics. Fixes #1917.
    Opaque(String),
}

impl TrustVcType {
    /// Returns the bit width, or `None` for non-bitvector types.
    ///
    /// Returns `None` for `Bool` and `MathInt` — these are not bitvector types
    /// and have no meaningful bit width. Returning `Some(0)` previously caused
    /// `parse_cast_expr` to attempt `bvextract(inner, u32::MAX, 0)` on
    /// narrowing casts to bool (#1950).
    #[must_use]
    pub fn bit_width(&self) -> Option<u32> {
        match self {
            TrustVcType::Int { width } | TrustVcType::Uint { width } => Some(*width),
            TrustVcType::Char => Some(32),
            _ => None,
        }
    }

    /// Returns true if this is an unsigned integer type.
    #[must_use]
    pub const fn is_unsigned(&self) -> bool {
        matches!(self, TrustVcType::Uint { .. } | TrustVcType::Char)
    }

    /// Returns true if this type contains an Opaque variant (including nested).
    /// Used by encoding diagnostics to detect silent opaque compatibility
    /// fallbacks before solver translation (#2224).
    #[must_use]
    pub fn contains_opaque(&self) -> bool {
        match self {
            TrustVcType::Opaque(_) => true,
            TrustVcType::Seq(inner)
            | TrustVcType::Array(inner, _)
            | TrustVcType::Set(inner)
            | TrustVcType::Multiset(inner) => inner.contains_opaque(),
            TrustVcType::Map(key, value) => key.contains_opaque() || value.contains_opaque(),
            TrustVcType::SpecFn(args, ret) => {
                args.iter().any(TrustVcType::contains_opaque) || ret.contains_opaque()
            }
            TrustVcType::Datatype { variants, .. } => variants
                .iter()
                .any(|variant| variant.fields.iter().any(|(_, ty)| ty.contains_opaque())),
            _ => false,
        }
    }

    /// Monomorphizes a (possibly generic) type by substituting `TypeParam`s with
    /// the given concrete `bindings` AND renaming any datatype carrier (and its
    /// self-recursive `RecursiveRef` edges) to the per-instantiation name.
    ///
    /// This is the shared building block both the constructor-call lowering and
    /// the source spec-function catalog use to turn a TEMPLATE carrier such as
    /// `GList` (`GCons(head: TypeParam("T"), tail: RecursiveRef("GList"))`) into a
    /// concrete per-instantiation carrier `GList<i32>`
    /// (`GCons(head: i32, tail: RecursiveRef("GList<i32>"))`), exactly mirroring
    /// how the builtin `List<i32>` already substitutes a concrete element sort.
    ///
    /// Soundness-critical invariants (preserve the #99/#100 datatype guards):
    ///   * The recursion edge stays a SELF-only `RecursiveRef` pointing at THIS
    ///     monomorphized carrier — never a cross-carrier edge (which the
    ///     well-foundedness validator rejects as unsupported mutual recursion).
    ///   * Distinct instantiations (`GList<i32>` vs `GList<bool>`) produce
    ///     DISTINCT carrier names — they are never collapsed into one carrier.
    ///
    /// With empty `bindings` the type is returned structurally unchanged (no
    /// carrier renaming): a carrier is renamed only when a concrete instantiation
    /// is actually being applied.
    #[must_use]
    pub fn monomorphize(&self, bindings: &[(String, TrustVcType)]) -> TrustVcType {
        self.monomorphize_carrier(bindings, None)
    }

    /// Internal worker for [`Self::monomorphize`]. `enclosing` carries the
    /// (template_name, template_base, concrete_name) of the nearest enclosing
    /// datatype carrier so a self-`RecursiveRef` inside its fields can be retargeted
    /// to the freshly minted per-instantiation carrier name.
    fn monomorphize_carrier(
        &self,
        bindings: &[(String, TrustVcType)],
        enclosing: Option<(&str, &str, &str)>,
    ) -> TrustVcType {
        match self {
            TrustVcType::TypeParam(name) => bindings
                .iter()
                .find_map(|(param, concrete)| (param == name).then(|| concrete.clone()))
                .unwrap_or_else(|| self.clone()),
            TrustVcType::RecursiveRef(target) => {
                if let Some((tmpl_name, tmpl_base, concrete_name)) = enclosing {
                    if target == tmpl_name || datatype_base_name(target) == tmpl_base {
                        return TrustVcType::RecursiveRef(concrete_name.to_string());
                    }
                }
                self.clone()
            }
            TrustVcType::Seq(inner) => {
                TrustVcType::Seq(Box::new(inner.monomorphize_carrier(bindings, enclosing)))
            }
            TrustVcType::Array(inner, len) => TrustVcType::Array(
                Box::new(inner.monomorphize_carrier(bindings, enclosing)),
                *len,
            ),
            TrustVcType::Set(inner) => {
                TrustVcType::Set(Box::new(inner.monomorphize_carrier(bindings, enclosing)))
            }
            TrustVcType::Multiset(inner) => {
                TrustVcType::Multiset(Box::new(inner.monomorphize_carrier(bindings, enclosing)))
            }
            TrustVcType::Map(key, value) => TrustVcType::Map(
                Box::new(key.monomorphize_carrier(bindings, enclosing)),
                Box::new(value.monomorphize_carrier(bindings, enclosing)),
            ),
            TrustVcType::SpecFn(args, ret) => TrustVcType::SpecFn(
                args.iter()
                    .map(|arg| arg.monomorphize_carrier(bindings, enclosing))
                    .collect(),
                Box::new(ret.monomorphize_carrier(bindings, enclosing)),
            ),
            TrustVcType::Datatype { name, variants } => {
                let base = datatype_base_name(name);
                let concrete_name = if bindings.is_empty() {
                    name.clone()
                } else {
                    let args = bindings
                        .iter()
                        .map(|(_, ty)| ty.to_type_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{base}<{args}>")
                };
                let child = (name.as_str(), base, concrete_name.as_str());
                TrustVcType::Datatype {
                    name: concrete_name.clone(),
                    variants: variants
                        .iter()
                        .map(|variant| {
                            DatatypeVariant::new(
                                variant.name.clone(),
                                variant
                                    .fields
                                    .iter()
                                    .map(|(field, field_ty)| {
                                        (
                                            field.clone(),
                                            field_ty.monomorphize_carrier(bindings, Some(child)),
                                        )
                                    })
                                    .collect(),
                            )
                        })
                        .collect(),
                }
            }
            _ => self.clone(),
        }
    }

    /// Returns true if this type is or contains a `TypeParam` (i.e. it is a
    /// generic TEMPLATE that has not been monomorphized to a concrete type).
    #[must_use]
    pub fn contains_type_param(&self) -> bool {
        match self {
            TrustVcType::TypeParam(_) => true,
            TrustVcType::Seq(inner)
            | TrustVcType::Array(inner, _)
            | TrustVcType::Set(inner)
            | TrustVcType::Multiset(inner) => inner.contains_type_param(),
            TrustVcType::Map(key, value) => {
                key.contains_type_param() || value.contains_type_param()
            }
            TrustVcType::SpecFn(args, ret) => {
                args.iter().any(TrustVcType::contains_type_param) || ret.contains_type_param()
            }
            TrustVcType::Datatype { variants, .. } => variants.iter().any(|variant| {
                variant
                    .fields
                    .iter()
                    .any(|(_, ty)| ty.contains_type_param())
            }),
            _ => false,
        }
    }

    /// Infers concrete `TypeParam` bindings by structurally matching `self` (a
    /// template type that may mention `TypeParam`s) against `actual` (a concrete
    /// type). E.g. matching the template carrier `GList`
    /// (`GCons(head: TypeParam("T"), ..)`) against the concrete carrier
    /// `GList<i32>` (`GCons(head: i32, ..)`) records `("T", i32)`.
    ///
    /// First binding wins; later conflicting matches for the same parameter are
    /// ignored (so an inconsistent use site never silently rebinds). Used by the
    /// source spec-function catalog to discover the instantiation a generic spec
    /// fn must be monomorphized to.
    pub fn collect_type_param_bindings(
        &self,
        actual: &TrustVcType,
        bindings: &mut Vec<(String, TrustVcType)>,
    ) {
        match (self, actual) {
            (TrustVcType::TypeParam(name), concrete)
                if !matches!(concrete, TrustVcType::TypeParam(_)) =>
            {
                if !bindings.iter().any(|(existing, _)| existing == name) {
                    bindings.push((name.clone(), concrete.clone()));
                }
            }
            (TrustVcType::Seq(a), TrustVcType::Seq(b))
            | (TrustVcType::Set(a), TrustVcType::Set(b))
            | (TrustVcType::Multiset(a), TrustVcType::Multiset(b))
            | (TrustVcType::Array(a, _), TrustVcType::Array(b, _)) => {
                a.collect_type_param_bindings(b, bindings);
            }
            (TrustVcType::Map(ak, av), TrustVcType::Map(bk, bv)) => {
                ak.collect_type_param_bindings(bk, bindings);
                av.collect_type_param_bindings(bv, bindings);
            }
            (TrustVcType::SpecFn(aargs, aret), TrustVcType::SpecFn(bargs, bret)) => {
                for (a, b) in aargs.iter().zip(bargs.iter()) {
                    a.collect_type_param_bindings(b, bindings);
                }
                aret.collect_type_param_bindings(bret, bindings);
            }
            (
                TrustVcType::Datatype {
                    variants: avariants,
                    ..
                },
                TrustVcType::Datatype {
                    variants: bvariants,
                    ..
                },
            ) => {
                for (av, bv) in avariants.iter().zip(bvariants.iter()) {
                    for ((_, af), (_, bf)) in av.fields.iter().zip(bv.fields.iter()) {
                        af.collect_type_param_bindings(bf, bindings);
                    }
                }
            }
            _ => {}
        }
    }

    /// Returns true if this type is or contains a floating-point type (f32/f64).
    /// Used to reject float-typed variables before encoding — IEEE 754 semantics
    /// are not modeled, so mapping to `Sort::Real` would produce false positives (#1735).
    #[must_use]
    pub fn contains_float(&self) -> bool {
        match self {
            TrustVcType::Float { .. } => true,
            TrustVcType::Seq(inner)
            | TrustVcType::Array(inner, _)
            | TrustVcType::Set(inner)
            | TrustVcType::Multiset(inner) => inner.contains_float(),
            TrustVcType::Map(key, value) => key.contains_float() || value.contains_float(),
            TrustVcType::SpecFn(args, ret) => {
                args.iter().any(TrustVcType::contains_float) || ret.contains_float()
            }
            _ => false,
        }
    }

    /// Returns true if this is a spec collection (Seq, Set, Map).
    #[must_use]
    pub const fn is_collection(&self) -> bool {
        matches!(
            self,
            TrustVcType::Seq(_)
                | TrustVcType::Array(_, _)
                | TrustVcType::Set(_)
                | TrustVcType::Multiset(_)
                | TrustVcType::Map(_, _)
        )
    }

    /// Returns true if this runtime type exposes a collection view.
    #[must_use]
    pub const fn is_string_like(&self) -> bool {
        matches!(self, TrustVcType::StrSlice | TrustVcType::String)
    }

    /// Returns true if this type needs sequence-length tracking.
    #[must_use]
    pub fn has_collection_length(&self) -> bool {
        self.is_collection() || self.is_string_like()
    }

    /// Returns the spec-collection type exposed by this value's `view()` surface.
    #[must_use]
    pub fn view_collection_type(&self) -> Option<TrustVcType> {
        match self {
            TrustVcType::Seq(_)
            | TrustVcType::Set(_)
            | TrustVcType::Multiset(_)
            | TrustVcType::Map(_, _) => Some(self.clone()),
            TrustVcType::Array(elem, _) => Some(TrustVcType::Seq(elem.clone())),
            TrustVcType::StrSlice | TrustVcType::String => {
                Some(TrustVcType::Seq(Box::new(TrustVcType::Char)))
            }
            _ => None,
        }
    }

    /// Returns the erased inner type for the verifier-supported `Cow<'_, T>`
    /// subset.
    #[must_use]
    pub fn cow_inner_type(&self) -> Option<TrustVcType> {
        let TrustVcType::Datatype { name, variants } = self else {
            return None;
        };
        if !name.starts_with("Cow<") {
            return None;
        }

        let borrowed_ty = variants
            .iter()
            .find(|variant| variant.name == "Borrowed")
            .and_then(|variant| variant.fields.first())
            .map(|(_, ty)| ty.clone())?;
        let owned_ty = variants
            .iter()
            .find(|variant| variant.name == "Owned")
            .and_then(|variant| variant.fields.first())
            .map(|(_, ty)| ty.clone())?;

        (borrowed_ty == owned_ty).then_some(borrowed_ty)
    }

    /// Returns true for the verifier-supported `Cow<'_, T>` datatype shape.
    #[must_use]
    pub fn is_cow(&self) -> bool {
        self.cow_inner_type().is_some()
    }

    /// Returns the view type exposed by the narrow Cow lowering subset.
    ///
    /// This intentionally covers only string-like views and single-field source
    /// structs. Other Cow receivers fail closed during lowering until TrustVc has
    /// a general `View` trait model.
    #[must_use]
    pub fn cow_view_type(&self) -> Option<TrustVcType> {
        let inner = self.cow_inner_type()?;
        inner
            .view_collection_type()
            .or_else(|| single_field_datatype_field_type(&inner))
    }

    /// Returns the element type for collection types (#2067).
    /// `Seq<T>` -> `T`, `Set<T>` -> `T`, `Map<K, V>` -> `V`.
    #[must_use]
    pub fn collection_elem(&self) -> Option<TrustVcType> {
        match self {
            TrustVcType::Seq(e)
            | TrustVcType::Array(e, _)
            | TrustVcType::Set(e)
            | TrustVcType::Multiset(e) => Some((**e).clone()),
            TrustVcType::Map(_, v) => Some((**v).clone()),
            _ => None,
        }
    }

    /// Returns true if this is an integer type (signed or unsigned BV).
    #[must_use]
    pub const fn is_integer(&self) -> bool {
        matches!(self, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
    }

    /// Validates that recursive datatypes have a structurally decreasing shape.
    ///
    /// The current IR models only self-recursive carriers via `RecursiveRef`.
    /// Built-in recursive datatypes such as `List<T>` and `Tree<T>` are
    /// well-founded because they include a base-case variant that breaks the
    /// recursion. Datatypes whose variants all recurse back to the same carrier
    /// are rejected before encoder registration.
    ///
    /// Cross-datatype `RecursiveRef` edges are also rejected for now. They
    /// would require SCC-level validation across a datatype graph, which the
    /// current datatype registration path does not model yet.
    /// Legacy compatibility wrapper for callers that still expect a human-facing
    /// string error. Prefer `try_validate_well_foundedness` for typed handling.
    pub fn validate_well_foundedness(&self) -> Result<(), String> {
        self.try_validate_well_foundedness()
            .map_err(|err| err.to_string())
    }

    /// Typed well-foundedness validation for programmatic callers.
    pub fn try_validate_well_foundedness(&self) -> Result<(), DatatypeWellFoundednessError> {
        let TrustVcType::Datatype { name, variants } = self else {
            return Ok(());
        };

        let mut recursive_targets = BTreeSet::new();
        let mut has_self_recursive_variant = false;
        let mut has_base_case_variant = false;

        for variant in variants {
            let mut variant_recurses_to_self = false;
            for (_, field_ty) in &variant.fields {
                match field_ty {
                    TrustVcType::RecursiveRef(target) if target == name => {
                        has_self_recursive_variant = true;
                        variant_recurses_to_self = true;
                    }
                    TrustVcType::RecursiveRef(target) => {
                        recursive_targets.insert(target.clone());
                    }
                    _ => {}
                }
            }

            if !variant_recurses_to_self {
                has_base_case_variant = true;
            }
        }

        if !recursive_targets.is_empty() {
            let targets = recursive_targets.into_iter().collect::<Vec<_>>().join(", ");
            return Err(DatatypeWellFoundednessError::MutualRecursionUnsupported {
                datatype: name.clone(),
                targets,
            });
        }

        if !has_self_recursive_variant || has_base_case_variant {
            return Ok(());
        }

        Err(DatatypeWellFoundednessError::NoBaseCase {
            datatype: name.clone(),
        })
    }
}

/// The carrier base name with any `<..>` generic-argument suffix stripped
/// (`List<i32>` -> `List`, `GList` -> `GList`).
fn datatype_base_name(name: &str) -> &str {
    name.split('<').next().unwrap_or(name)
}

fn single_field_datatype_field_type(ty: &TrustVcType) -> Option<TrustVcType> {
    let TrustVcType::Datatype { variants, .. } = ty else {
        return None;
    };
    let [variant] = variants.as_slice() else {
        return None;
    };
    let [(_, field_ty)] = variant.fields.as_slice() else {
        return None;
    };
    Some(field_ty.clone())
}

#[cfg(test)]
#[path = "ir_tests.rs"]
mod tests;
