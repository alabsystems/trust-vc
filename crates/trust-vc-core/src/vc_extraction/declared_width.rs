// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `let` ANNOTATION WIDTH CARRY — the syntactic shape of a `let` type
//! ascription, and a lockstep walk that re-spells the initializer's bare
//! integer literals at the width the ascription fixes.
//!
//! THE HOLE THIS CLOSES (measured on the HEAD lens, 2026-09-18, ay
//! 0.27.0@`c1dd8ecb`). `vc_extraction::single_typed_int_bindings` and
//! `body_extract::local_pat_declared_int_suffix` record a `let` ascription only
//! for a BARE primitive-integer binding, so
//! `let v: Vec<u8> = vec![200]; v[0usize] + 100` rendered its element as the
//! `i32` placeholder, discharged the addition at 32 bits and VERIFIED a program
//! that panics on `u8` overflow. The same hole reached `Option<u8>`, `[u8; k]`,
//! tuples, `&u8`, `&[u8]`, `core::primitive::u8` and file-local `type` aliases.
//!
//! THE MECHANISM IS THE EXISTING ONE, NOT A NEW CHANNEL. The suffixed spellings
//! `vec![200u8]` / `Some(200u8)` are ALREADY correctly refuted (measured: both
//! are `Counterexample` at HEAD) because the suffix survives into the rendered
//! obligation text and is re-read by `ir_lowering::atoms::type_from_int_suffix`.
//! So this module makes the broken spellings render as the spellings that
//! already work; no IR, encoder or type channel changes.
//!
//! THE ADMISSION RULE IS A CLOSED WORLD, NOT A LIST OF ESCAPES (2026-09-18,
//! round 5). Four review rounds each found a new construct that binds a type
//! name without appearing in this file's item list — a nested `mod`, a glob, a
//! body-scope `use`, a captured `core::primitive::` prefix — and each was
//! answered by REFUSING that shape. Round 5 found four more, and one of them
//! settles the question: a `#[derive(..)]` or an attribute proc macro can
//! inject `pub type u32 = u64;` into the enclosing module (MEASURED with a
//! dependency-free proc-macro crate: `size_of::<u32>()` is 8 in a file whose
//! only unusual text is `#[derive(Widen)] pub struct S;`), and INERTNESS OF AN
//! ATTRIBUTE IS NOT SYNTACTICALLY DECIDABLE. The escape set is therefore not
//! enumerable, and a denylist can never be finished.
//!
//! So the default is inverted. [`FileTypeNames::enumerable`] is a CLOSED-WORLD
//! admission: the lane runs only over files built from a fixed, modelled set of
//! constructs whose binding effect this module can read off the text, and ANY
//! construct outside that set — an unmodelled `syn::Item` variant, an
//! item-position macro INVOCATION, an `extern crate`, a `#[cfg]`, a non-builtin
//! `derive`, an unknown attribute, a glob — turns the lane OFF for the whole
//! file. "Off" means [`Wid::Opaque`]: carry nothing, refuse nothing, HEAD's
//! rendering byte-for-byte. Unknown text can only cost capability, never
//! soundness, and nothing new has to be enumerated when Rust grows a feature.
//!
//! WHAT ROUND 5 MEASURED, and what it costs (`fv3` lens pair, dev tree vs a
//! pristine `bbb3250b` export, each in its OWN target dir; stock-rustc twins at
//! `-C overflow-checks=on` for truth):
//! * `macro_rules! d { () => { pub type u64 = ::core::primitive::u32; } } d!();`
//!   — the expansion really does rebind `u64` file-wide (`elem_bytes=4`), the
//!   carry attached `u64` and VERIFIED a program that panics. Every invocation
//!   spelling leaks the same way (`d!();`, `d!{}`, `d![]`, macro-invokes-macro).
//! * `extern crate self as core;` — captures the extern prelude, so BOTH
//!   `core::primitive::u64` AND `::core::primitive::u64` denote the file's own
//!   `mod primitive` (MEASURED: `lead_bytes=4`). The leading-`::` spelling this
//!   module used to call capture-proof is only capture-proof against a glob and
//!   a `mod core`, which is what had been measured; an `extern crate` beats it.
//! * A FILE-SCOPE `type u32 = ::core::primitive::u64;` read for a function
//!   written INSIDE an inline `mod` — the alias does not apply there (items are
//!   not inherited by submodules), the element is really four bytes, and the
//!   carry VERIFIED a panicking program. This one is not about macros at all:
//!   it is the file-scope table being applied in a scope it cannot speak for.
//!   Answered by [`FileTypeNames::has_inline_mod`], which makes every
//!   FILE-DECLARED name `Undecided` once the file holds an inline module.
//! * The same blindness in the narrow direction REFUTED true claims HEAD
//!   verified (`type u8 = ::core::primitive::u64;` behind a macro, and the
//!   `extern crate` twin). Those are restored: an unenumerable file carries
//!   nothing, so the verdict is HEAD's.
//!
//! SOUNDNESS. A Rust `let` ascription is a COMPLETE type constraint at that
//! node: the initializer is unified with the ascribed type and integer-literal
//! inference at a position that unification fixes is settled — no later use can
//! move it without making the program a type error. So the suffix attached here
//! is the width rustc infers, PROVIDED four premises, each discharged by a
//! check that REFUSES (or, for premise (0), silently declines) rather than
//! proceeds when it fails:
//!   (0) the file's text ENUMERATES every binding that can reach the function —
//!       [`FileTypeNames::enumerable`], the closed world above;
//!   (i) the ascription's names denote the types they spell —
//!       [`FileTypeNames`] resolves file-local `type` aliases and treats any
//!       file-declared or explicitly imported name as NOT the primitive it
//!       spells (`type u64 = u8; let x: u64 = 200;` was a live false
//!       `Verified`; it is now decided through the alias, not the spelling);
//!   (ii) the constructor spine is the std one — `Some` / `None` / `vec!` /
//!       `Vec` shadowed by a file item refuse ([`ERR_SHADOWED_CTOR`]);
//!   (iii) the literal fits its declared leaf ([`ERR_RANGE`]) — an
//!       out-of-range literal is not a well-typed program, and rendering
//!       `300u8` would hand the encoder a token that does not denote what it
//!       looks like.
//! Where the ascription does NOT fix a literal's position — a call argument, an
//! arithmetic operand, a struct field, an index — the walk stops with it: it
//! REFUSES when a non-default width is in play at that position (so we know a
//! width would be dropped, [`ERR_WALL`]) and otherwise leaves today's rendering
//! byte-identical. That boundary is what separates this from H1b (a literal
//! with NO ascription anywhere), which stays open.
//!
//! FAIL-CLOSED DIRECTION. Every path here has exactly three outcomes: render a
//! suffix that is provably rustc's type; return `Ok(None)` and produce
//! byte-identical text to HEAD; or return an `Err` that stops extraction. A
//! suffix can only NARROW the width an obligation is discharged at (from the
//! 32-bit default down to the declared width), and narrowing an integer sort
//! can only ADD counterexamples, never remove them.
//!
//! THE ONE RESIDUAL THE CLOSED WORLD CANNOT REACH, stated rather than hidden:
//! the extern prelude is a CRATE-level property, so a crate root that writes
//! `extern crate self as core;` rebinds `::core` for every module file of that
//! crate, and a single-file scan cannot see it. That premise is not new to this
//! lane — the whole extraction already reads `Vec`, `Option`, `Some`, `None`
//! and `vec!` as the `std` ones — and it is the same boundary as the recorded
//! "no file context" residual. It is the only way a file this module calls
//! ENUMERABLE can still be wrong, and closing it needs crate-level context.
//!
//! FLOATS ARE DELIBERATELY NOT CARRIED, on a measurement. The go/no-go probe
//! for this increment asked whether a suffixed float literal inside a composite
//! is refuted: `let v: Vec<f32> = vec![16777216.0f32]; v[0usize] + 1.0f32 >
//! v[0usize]` returns `NotProved { category: Incompleteness }`, not a
//! refutation, so re-spelling the bare form would trade a false `Verified` for
//! a fail-closed `Unknown` on every `f32` container rather than for a genuine
//! counterexample. Float leaves are therefore [`Wid::Neutral`]: rendered
//! unchanged (today's behaviour exactly, no new refusal) and NEVER counted as
//! width-decided, so the Option payload lane's float rule is untouched. The
//! bare-`f32`-container false `Verified` is a RECORDED RESIDUAL of this
//! increment, not a closed hole.

use std::collections::{BTreeMap, BTreeSet};

use quote::ToTokens;
use syn::{Expr, Type};

use crate::error::TrustVcError;

/// R2(a). A bare numeric literal reached a position the file cannot resolve to
/// a primitive: an imported or user name, a generic parameter, a qualified or
/// associated path, `impl Trait`, or an alias whose resolution cycles or takes
/// generic parameters.
pub(crate) const ERR_UNDECIDED: &str = "a `let` type annotation this extraction cannot resolve to a primitive carries an unsuffixed numeric literal";

/// R2(b). A bare numeric literal inside an expression that is NOT on the
/// admitted constructor spine, at a position whose declared shape holds a
/// non-default integer leaf.
pub(crate) const ERR_WALL: &str = "an unsuffixed numeric literal sits inside an expression the declared-width walk does not model, at a position whose `let` annotation fixes a non-default integer width";

/// R2(c). The literal's magnitude is outside the sign-aware range of its
/// declared leaf.
pub(crate) const ERR_RANGE: &str =
    "an integer literal does not fit the width its `let` annotation declares";

/// R2(d). The declared shape and the initializer's shape disagree while a
/// non-default integer width is in play.
pub(crate) const ERR_ARITY: &str = "the `let` annotation's shape and its initializer's shape disagree while a non-default integer width is in play";

/// R2(e). `Some` / `None` / `Vec` / `vec!` used on the spine when the file
/// declares or imports an item of that name.
pub(crate) const ERR_SHADOWED_CTOR: &str = "the `let` initializer's constructor is shadowed by a file item, so it need not be the `std` constructor whose payload type the annotation fixes";

/// The common prefix every refusal above is reported under, so one needle
/// matches the whole family and each arm keeps its own text.
pub(crate) const REFUSAL_PREFIX: &str = "`let` annotation width carry: ";

pub(crate) fn refusal(arm: &str, ty: &Type, expr: &Expr) -> TrustVcError {
    TrustVcError::Encoding {
        context: "extract body assertions",
        detail: format!(
            "{REFUSAL_PREFIX}{arm}. Rust gives the literal the annotation's type, which the \
             rendered value would drop (it re-lowers at the `i32` default), so it is refused \
             rather than checked at the wrong width. Annotation `{}`, at `{}`.",
            ty.to_token_stream(),
            expr.to_token_stream()
        ),
    }
}

/// The syntactic width map of a `let` type ascription.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Wid {
    /// A primitive integer type OTHER than `i32`, spelled VERBATIM. `usize` /
    /// `isize` are never frozen to a concrete width here, so a
    /// `global size_of usize` directive still applies at re-lowering.
    Scalar(&'static str),
    /// `i32`: decided, and already the rendering default, so nothing is
    /// carried. Counted as width-decided.
    DefaultInt,
    /// A decided leaf that carries no integer width and is NOT counted as
    /// width-decided: `f32` / `f64` (see the module header), `bool`, `char`,
    /// `str`, `()`.
    Neutral,
    Opt(Box<Wid>),
    Vector(Box<Wid>),
    /// `[T; k]` and `[T]`.
    Seq(Box<Wid>),
    Tuple(Vec<Wid>),
    Ref(Box<Wid>),
    /// THE LANE IS OFF FOR THIS FILE. Produced for every leaf of every
    /// ascription once [`FileTypeNames::enumerable`] is false, i.e. once the
    /// file holds any construct whose bindings this module cannot read off the
    /// text (an item-position macro invocation, an `extern crate`, a `#[cfg]`,
    /// a non-builtin `derive`, an unknown attribute, a glob, an unmodelled item
    /// kind).
    ///
    /// Deliberately NOT [`Wid::Undecided`]: refusing would turn ordinary code
    /// into an error. `Opaque` is the third outcome — carry nothing, refuse
    /// nothing, keep HEAD's rendering byte-for-byte.
    ///
    /// The payload is the suffix handed to [`scalar_int_suffix`] ONLY, and it
    /// is `Some` on EXACTLY the shape HEAD's two bare-scalar recorders accepted
    /// (a single-segment, leading-colon-free, argument-free primitive name), so
    /// those recorders behave byte-for-byte as they did before this lane
    /// existed. Their blindness to an unenumerable file is PRE-EXISTING and
    /// stays recorded open; what this lane must not do is extend it into
    /// composites, where it flips a correct `Counterexample` to a false
    /// `Verified`. `None` is every other spelling: no suffix, no carry, no
    /// refusal.
    Opaque(Option<&'static str>),
    /// NOT syntactically determined by this file.
    Undecided,
}

impl Wid {
    /// True when this shape holds a non-default integer leaf anywhere, i.e. a
    /// width would actually be dropped by rendering a bare literal into it.
    pub(crate) fn holds_width(&self) -> bool {
        match self {
            Wid::Scalar(_) => true,
            Wid::DefaultInt | Wid::Neutral | Wid::Undecided | Wid::Opaque(_) => false,
            Wid::Opt(inner) | Wid::Vector(inner) | Wid::Seq(inner) | Wid::Ref(inner) => {
                inner.holds_width()
            }
            Wid::Tuple(elems) => elems.iter().any(Wid::holds_width),
        }
    }
}

/// The primitive-type leaf classifier. ONE place decides what a primitive type
/// name means, shared by [`shape_of`], `vc_extraction::single_typed_bindings`
/// and `body_extract::local_pat_declared_int_suffix` (which previously
/// hand-rolled two different, and differently wrong, versions: one used
/// `path.get_ident()` and so rejected a leading `::`, the other checked qself,
/// segment count and arguments but never `leading_colon`).
fn primitive_leaf(ident: &str) -> Option<Wid> {
    match ident {
        "i32" => Some(Wid::DefaultInt),
        "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16" | "i64" | "i128"
        | "isize" => Some(Wid::Scalar(match ident {
            "u8" => "u8",
            "u16" => "u16",
            "u32" => "u32",
            "u64" => "u64",
            "u128" => "u128",
            "usize" => "usize",
            "i8" => "i8",
            "i16" => "i16",
            "i64" => "i64",
            "i128" => "i128",
            _ => "isize",
        })),
        "f32" | "f64" | "bool" | "char" | "str" => Some(Wid::Neutral),
        // The ghost math types. `int` / `nat` are unbounded, so no width is
        // dropped by leaving their literals bare — and they are spelled by a
        // glob-imported prelude name in nearly every ported corpus file, so
        // reading them as `Undecided` would refuse ordinary spec code.
        "int" | "nat" => Some(Wid::Neutral),
        _ => None,
    }
}

/// Every type name the FILE binds, plus its resolvable `type` aliases.
///
/// Built once per extraction beside `file_shadowing_mut_receiver_methods`. When
/// the function's source file is not known the table is ABSENT and this whole
/// lane is off — no carry and no refusal, today's behaviour byte-for-byte (a
/// scoping decision, recorded as a residual and pinned by a unit test, not
/// claimed closed).
#[derive(Clone, Default)]
pub(crate) struct FileTypeNames {
    /// File-local `type X = T;` with no generic parameters and no `where`.
    aliases: BTreeMap<String, Type>,
    /// Names the file DECLARES as items (`type`, `struct`, `enum`, `fn`,
    /// `const`, `mod`, `macro_rules!`, …). Such a name is never read as the
    /// primitive it spells.
    declared_names: BTreeSet<String>,
    /// Leaf names of the file's explicit `use` items, including `as` renames.
    /// An import can shadow a primitive too, but an import that spells a
    /// WIDTH-FREE primitive is still read as that primitive — see
    /// [`shape_of`]: rendering is unchanged for a width-free leaf, so the
    /// carve-out can never attach a wrong width, and without it every ported
    /// corpus file that writes `use ...::{int, nat};` would refuse its own
    /// `let _: int = 10;` (measured: 29 functions across 7 files).
    imported_names: BTreeSet<String>,
    /// Every name bound by a scope this file-scope table cannot speak for: an
    /// INLINE `mod` at any depth, and — since 2026-09-18 — any `use`, `type`,
    /// `fn`, `struct`, `const`, … item written INSIDE a function body or a
    /// nested block, at any depth.
    ///
    /// The table is built once per FILE but applied to a function in ANY scope,
    /// and `extract_verification_conditions_with_file_context` is handed no
    /// module path, so neither direction of a nested rebinding can be resolved:
    /// a function inside `mod inner { type W = i32; }` must NOT read the
    /// file-scope `type W = i64;`, and a nested `type u64 = u8;` shadows the
    /// primitive for the functions inside that module. Both were measured as
    /// false `Verified`s. A name in this set is therefore `Undecided`
    /// everywhere in the file — REFUSE rather than guess which scope the
    /// function came from.
    ///
    /// A BODY-scope `use` is the same class and was measured the same way:
    /// `type Id = u64; fn f() { use other::Id; let v: Vec<Id> = vec![3000000000]; … }`
    /// and `fn f() { use other::u64; let v: Vec<u64> = …; }` were false
    /// `Verified`s whose stock-rustc twins panic (`elem_size=4`), because the
    /// file-scope table saw only `type Id = u64` (or the primitive `u64`) and
    /// never the import that rebinds it inside the body. A body `use` also
    /// shadows for the REST of that body only, which is one more scope this
    /// table has no way to represent — so the name is poisoned file-wide.
    nested_bound_names: BTreeSet<String>,
    /// True when the file carries at least one glob `use ...::*;`, at FILE
    /// scope, inside an inline `mod`, or inside a function body / nested block.
    /// A glob cannot be enumerated and CAN rebind a primitive type name — and
    /// can rebind `core` / `std` themselves, so the unqualified
    /// `core::primitive::uN` spelling is NOT glob-proof either (measured with
    /// rustc: a glob-imported `m::core` makes `core::primitive::u8` eight bytes
    /// wide, while `::core::primitive::u8` in the same file stays one). Every
    /// width-BEARING primitive spelling that is not written with a leading `::`
    /// therefore becomes [`Wid::Opaque`]. See that variant for why this is not
    /// `Undecided`.
    has_glob_import: bool,
    /// THE CLOSED-WORLD ADMISSION. True only when every construct the file
    /// holds is one this module MODELS, so the text really does enumerate every
    /// binding that can reach a function in it. See the module header for why
    /// this is an allowlist rather than a denylist; [`file_is_enumerable`] is
    /// the predicate. When it is false the whole lane is off for the file and
    /// every leaf is [`Wid::Opaque`].
    enumerable: bool,
    /// True when the file holds an inline `mod … { … }`. A submodule does NOT
    /// inherit its parent's items, and this table is built per FILE while
    /// `extract_verification_conditions_with_file_context` is handed no module
    /// path — so a FILE-DECLARED name cannot be resolved for a function that
    /// may live inside that module. MEASURED as a false `Verified`:
    /// `type u32 = ::core::primitive::u64; mod inner { fn f() { let v: Vec<u32>
    /// = vec![3000000000]; … } }` carried `u64` while the element is really
    /// four bytes wide and the program panics. Every file-declared name is
    /// therefore `Undecided` once this is set — REFUSE rather than guess which
    /// scope the function came from. (Names an inline module BINDS were already
    /// poisoned the same way; see `nested_bound_names`. This is the other
    /// direction of the same ambiguity.)
    has_inline_mod: bool,
}

impl std::fmt::Debug for FileTypeNames {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FileTypeNames")
            .field("aliases", &self.aliases.keys().collect::<Vec<_>>())
            .field("declared_names", &self.declared_names)
            .field("imported_names", &self.imported_names)
            .field("nested_bound_names", &self.nested_bound_names)
            .field("has_glob_import", &self.has_glob_import)
            .field("enumerable", &self.enumerable)
            .field("has_inline_mod", &self.has_inline_mod)
            .finish()
    }
}

impl FileTypeNames {
    pub(crate) fn from_file(file: &syn::File) -> Self {
        let mut names = FileTypeNames::default();
        names.absorb_items(&file.items);
        names.absorb_body_scopes(&file.items);
        // The admission runs LAST, because the `derive` arm asks whether the
        // file binds the name a built-in derive spells (`use m::Clone;` makes
        // `#[derive(Clone)]` a third-party macro again), and that needs the
        // name sets the two absorb passes just built.
        names.enumerable = !names.has_glob_import && file_is_enumerable(file, &names);
        names
    }

    /// Record every name bound INSIDE a function body or a nested block, at
    /// any depth and in any item of the file (free `fn`, inherent/trait `impl`
    /// method, defaulted trait method, and the same again inside an inline
    /// `mod`).
    ///
    /// `absorb_items` / `absorb_nested` see only ITEM lists, so a `use` written
    /// as a STATEMENT was invisible to both — the hole that made
    /// `fn f() { use other::Id; let v: Vec<Id> = vec![3000000000]; … }` a false
    /// `Verified`. Names found here join `nested_bound_names` (Undecided
    /// everywhere) and a glob found here sets `has_glob_import`, exactly as if
    /// it had been written at file scope.
    fn absorb_body_scopes(&mut self, items: &[syn::Item]) {
        for item in items {
            match item {
                syn::Item::Fn(it) => self.absorb_block_scope(&it.block),
                syn::Item::Impl(it) => {
                    for inner in &it.items {
                        if let syn::ImplItem::Fn(f) = inner {
                            self.absorb_block_scope(&f.block);
                        }
                    }
                }
                syn::Item::Trait(it) => {
                    for inner in &it.items {
                        if let syn::TraitItem::Fn(f) = inner {
                            if let Some(block) = &f.default {
                                self.absorb_block_scope(block);
                            }
                        }
                    }
                }
                syn::Item::Mod(it) => {
                    if let Some((_, inner)) = &it.content {
                        self.absorb_body_scopes(inner);
                    }
                }
                _ => {}
            }
        }
    }

    fn absorb_block_scope(&mut self, block: &syn::Block) {
        let mut scan = BodyScopeScan {
            names: &mut self.nested_bound_names,
            glob: &mut self.has_glob_import,
        };
        syn::visit::Visit::visit_block(&mut scan, block);
    }

    fn absorb_items(&mut self, items: &[syn::Item]) {
        for item in items {
            match item {
                syn::Item::Type(item_type) => {
                    self.declared_names.insert(item_type.ident.to_string());
                    if item_type.generics.params.is_empty()
                        && item_type.generics.where_clause.is_none()
                    {
                        self.aliases
                            .insert(item_type.ident.to_string(), (*item_type.ty).clone());
                    }
                }
                syn::Item::Struct(it) => {
                    self.declared_names.insert(it.ident.to_string());
                }
                syn::Item::Enum(it) => {
                    self.declared_names.insert(it.ident.to_string());
                }
                syn::Item::Union(it) => {
                    self.declared_names.insert(it.ident.to_string());
                }
                syn::Item::Trait(it) => {
                    self.declared_names.insert(it.ident.to_string());
                }
                syn::Item::TraitAlias(it) => {
                    self.declared_names.insert(it.ident.to_string());
                }
                syn::Item::Fn(it) => {
                    self.declared_names.insert(it.sig.ident.to_string());
                }
                syn::Item::Const(it) => {
                    self.declared_names.insert(it.ident.to_string());
                }
                syn::Item::Static(it) => {
                    self.declared_names.insert(it.ident.to_string());
                }
                syn::Item::Mod(it) => {
                    self.declared_names.insert(it.ident.to_string());
                    // A nested inline module's own items do not shadow at file
                    // scope, so they are NOT absorbed into `declared_names` or
                    // the alias table. They are recorded separately: this table
                    // is applied to functions in every scope, so a name the
                    // module rebinds cannot be resolved in either direction and
                    // becomes `Undecided`. See `nested_bound_names`.
                    //
                    // The CONVERSE ambiguity is `has_inline_mod`: a function
                    // written inside this module does not see the FILE's items
                    // either, so once any inline module exists, no file-declared
                    // name can be resolved for any function of the file.
                    if let Some((_, inner)) = &it.content {
                        self.has_inline_mod = true;
                        self.absorb_nested(inner);
                    }
                }
                syn::Item::Macro(it) => {
                    if let Some(ident) = &it.ident {
                        self.declared_names.insert(ident.to_string());
                    }
                    if let Some(last) = it.mac.path.segments.last() {
                        if last.ident == "macro_rules" {
                            // `macro_rules! vec { .. }` binds `vec`; syn puts
                            // the defined name in `it.ident`, already inserted.
                        }
                    }
                }
                syn::Item::Use(it) => self.absorb_use_tree(&it.tree),
                _ => {}
            }
        }
    }

    fn absorb_use_tree(&mut self, tree: &syn::UseTree) {
        match tree {
            syn::UseTree::Path(path) => self.absorb_use_tree(&path.tree),
            syn::UseTree::Name(name) => {
                self.imported_names.insert(name.ident.to_string());
            }
            syn::UseTree::Rename(rename) => {
                self.imported_names.insert(rename.rename.to_string());
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.absorb_use_tree(item);
                }
            }
            // A glob cannot be enumerated, and it CAN rebind a primitive type
            // name. Recorded rather than ignored: see `has_glob_import` and
            // `Wid::Opaque` — the lane declines to carry through a
            // width-bearing primitive spelling in a glob-bearing file, and
            // refuses nothing, so ordinary glob code (`use vstd::prelude::*;`)
            // keeps HEAD's behaviour exactly.
            syn::UseTree::Glob(_) => self.has_glob_import = true,
        }
    }

    /// Record every name an inline `mod` binds, at any depth. Only the NAMES
    /// are kept: a nested item neither shadows at file scope nor resolves as a
    /// file-scope alias, so all this table can honestly say about such a name
    /// is "this file cannot decide it".
    fn absorb_nested(&mut self, items: &[syn::Item]) {
        for item in items {
            match item {
                syn::Item::Type(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                }
                syn::Item::Struct(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                }
                syn::Item::Enum(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                }
                syn::Item::Union(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                }
                syn::Item::Trait(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                }
                syn::Item::TraitAlias(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                }
                syn::Item::Fn(it) => {
                    self.nested_bound_names.insert(it.sig.ident.to_string());
                }
                syn::Item::Const(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                }
                syn::Item::Static(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                }
                syn::Item::Macro(it) => {
                    if let Some(ident) = &it.ident {
                        self.nested_bound_names.insert(ident.to_string());
                    }
                }
                syn::Item::Mod(it) => {
                    self.nested_bound_names.insert(it.ident.to_string());
                    if let Some((_, inner)) = &it.content {
                        self.has_inline_mod = true;
                        self.absorb_nested(inner);
                    }
                }
                syn::Item::Use(it) => self.absorb_nested_use_tree(&it.tree),
                _ => {}
            }
        }
    }

    fn absorb_nested_use_tree(&mut self, tree: &syn::UseTree) {
        match tree {
            syn::UseTree::Path(path) => self.absorb_nested_use_tree(&path.tree),
            syn::UseTree::Name(name) => {
                self.nested_bound_names.insert(name.ident.to_string());
            }
            syn::UseTree::Rename(rename) => {
                self.nested_bound_names.insert(rename.rename.to_string());
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.absorb_nested_use_tree(item);
                }
            }
            syn::UseTree::Glob(_) => self.has_glob_import = true,
        }
    }

    /// True when the file declares OR imports `name`, so the name need not
    /// denote the `std` / primitive item it spells.
    /// Whether the lane is ON for this file: its text enumerates every
    /// binding that can reach a function in it (see the module header).
    pub(crate) fn enumerable(&self) -> bool {
        self.enumerable
    }

    pub(crate) fn binds(&self, name: &str) -> bool {
        self.declared_names.contains(name)
            || self.imported_names.contains(name)
            || self.nested_bound_names.contains(name)
    }

    /// True when a bare `name` in a type position of any function in this
    /// file can only denote an item the file declares at FILE scope: the file
    /// is enumerable (the closed world), holds no inline module (whose
    /// functions would not see file-scope items), declares `name`, and neither
    /// imports it, aliases it with `type`, nor binds it in any nested scope.
    pub(crate) fn denotes_file_scope_item(&self, name: &str) -> bool {
        self.enumerable
            && !self.has_inline_mod
            && self.declared_names.contains(name)
            && !self.imported_names.contains(name)
            && !self.nested_bound_names.contains(name)
            && !self.aliases.contains_key(name)
    }

    /// See [`FileTypeNames::enumerable`].
    pub(crate) fn is_enumerable(&self) -> bool {
        self.enumerable
    }
}

/// Collects every name a BODY scope binds. Used by
/// [`FileTypeNames::absorb_block_scope`]; see `nested_bound_names` for why the
/// answer is "this file cannot decide it" rather than a resolution.
struct BodyScopeScan<'a> {
    names: &'a mut BTreeSet<String>,
    glob: &'a mut bool,
}

impl BodyScopeScan<'_> {
    fn use_tree(&mut self, tree: &syn::UseTree) {
        match tree {
            syn::UseTree::Path(path) => self.use_tree(&path.tree),
            syn::UseTree::Name(name) => {
                self.names.insert(name.ident.to_string());
            }
            syn::UseTree::Rename(rename) => {
                self.names.insert(rename.rename.to_string());
            }
            syn::UseTree::Group(group) => {
                for item in &group.items {
                    self.use_tree(item);
                }
            }
            syn::UseTree::Glob(_) => *self.glob = true,
        }
    }
}

impl<'ast> syn::visit::Visit<'ast> for BodyScopeScan<'_> {
    fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
        self.use_tree(&item.tree);
    }
    fn visit_item_type(&mut self, item: &'ast syn::ItemType) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_type(self, item);
    }
    fn visit_item_struct(&mut self, item: &'ast syn::ItemStruct) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_struct(self, item);
    }
    fn visit_item_enum(&mut self, item: &'ast syn::ItemEnum) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_enum(self, item);
    }
    fn visit_item_union(&mut self, item: &'ast syn::ItemUnion) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_union(self, item);
    }
    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_trait(self, item);
    }
    fn visit_item_trait_alias(&mut self, item: &'ast syn::ItemTraitAlias) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_trait_alias(self, item);
    }
    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        self.names.insert(item.sig.ident.to_string());
        syn::visit::visit_item_fn(self, item);
    }
    fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_const(self, item);
    }
    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_static(self, item);
    }
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        self.names.insert(item.ident.to_string());
        syn::visit::visit_item_mod(self, item);
    }
    fn visit_item_macro(&mut self, item: &'ast syn::ItemMacro) {
        if let Some(ident) = &item.ident {
            self.names.insert(ident.to_string());
        }
        syn::visit::visit_item_macro(self, item);
    }
}

/// Built-in attributes the COMPILER handles: they cannot expand to items, so a
/// file that carries only these still enumerates its own bindings. Deliberately
/// a SHORT allowlist — anything absent is treated as a macro, which is the
/// fail-open direction (no carry, no refusal).
///
/// `cfg` / `cfg_attr` are ABSENT on purpose: `syn` does not evaluate them, so a
/// gated `type Byte = u8;` beside a gated-out `type Byte = u64;` would resolve
/// to whichever comes first. (The holder lane answers the identical problem the
/// same way — `holder_lane_file_admissible` / `file_items_carry_cfg_attr`.)
/// `test` / `bench` are absent too: they synthesise items.
const INERT_BUILTIN_ATTRS: &[&str] = &[
    "allow",
    "automatically_derived",
    "cold",
    "deprecated",
    "doc",
    "deny",
    "expect",
    "export_name",
    "forbid",
    "inline",
    "link_section",
    "must_use",
    "no_mangle",
    "non_exhaustive",
    "repr",
    "track_caller",
    "used",
    "warn",
];

/// Inner (`#![..]`) attributes admitted on top of [`INERT_BUILTIN_ATTRS`].
/// `no_implicit_prelude` is deliberately NOT here: it removes `Option`, `Some`,
/// `None`, `Vec` and `vec!` from scope, which every constructor-spine check in
/// this module assumes.
const INERT_INNER_ATTRS: &[&str] = &["feature", "no_std", "recursion_limit"];

/// The nine derives the LANGUAGE defines. Their expansion is specified to be
/// `impl` blocks, so they bind no type name. Any other derive path is a
/// third-party proc macro and can inject items (MEASURED — see the module
/// header).
const BUILTIN_DERIVES: &[&str] = &[
    "Clone",
    "Copy",
    "Debug",
    "Default",
    "Eq",
    "Hash",
    "Ord",
    "PartialEq",
    "PartialOrd",
];

/// Namespaces whose ATTRIBUTE macros are admitted.
///
/// * `rustfmt` / `clippy` are registered TOOL namespaces: the language
///   guarantees the compiler ignores them, so they are inert by construction.
/// * `trust_vc` is this workspace's own macro crate. Admitting it adds no trust
///   the tool does not already extend — every verdict it produces already
///   assumes those attributes do not rewrite the source it read — and the
///   premise is measured: no `quote!` in `crates/trust-vc/src` emits a `type`,
///   `struct`, `enum`, `union` or `mod` item.
///
/// A path is admitted only when the file does NOT bind its first segment, so a
/// `use my_macros as trust_vc;` cannot borrow the exemption.
const INERT_ATTR_NAMESPACES: &[&str] = &["clippy", "rustfmt", "trust_vc"];

/// THE CLOSED-WORLD ADMISSION (see the module header).
///
/// True only when every item of the file — at file scope and inside every
/// inline `mod`, at any depth — is a construct this module MODELS, and carries
/// only attributes that cannot expand to items. Anything else, INCLUDING a
/// `syn::Item` variant not named here, answers false.
///
/// The walk reaches EVERY `syn::Item` position the file has — file scope,
/// inside an inline `mod`, and inside a function BODY or a nested block, at any
/// depth — because a `#[derive(Widen)] struct S;` written inside a body injects
/// into that body's scope just as surely as one at file scope injects into the
/// module's.
///
/// SCOPED TO ITEM POSITIONS, deliberately. An attribute on an item INSIDE an
/// `impl` or a `trait` expands to impl/trait items, which cannot bind a
/// module-scope type name, and a macro in STATEMENT position binds only inside
/// the body that holds it — for the function under extraction that is already
/// fail-closed elsewhere (`Unsupported <m>!() in vc_extraction`, measured), and
/// for any other function it cannot reach this one.
fn file_is_enumerable(file: &syn::File, names: &FileTypeNames) -> bool {
    if !inert_attrs(&file.attrs, names, true) {
        return false;
    }
    let mut scan = ItemAdmission { names, ok: true };
    syn::visit::Visit::visit_file(&mut scan, file);
    scan.ok
}

struct ItemAdmission<'n> {
    names: &'n FileTypeNames,
    ok: bool,
}

impl<'ast> syn::visit::Visit<'ast> for ItemAdmission<'_> {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        if !item_is_enumerable(item, self.names) {
            self.ok = false;
        }
        syn::visit::visit_item(self, item);
    }
}

fn item_is_enumerable(item: &syn::Item, names: &FileTypeNames) -> bool {
    match item {
        syn::Item::Type(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Struct(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Enum(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Union(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Trait(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::TraitAlias(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Fn(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Const(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Static(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Use(it) => inert_attrs(&it.attrs, names, false),
        syn::Item::Impl(it) => inert_attrs(&it.attrs, names, false),
        // A `mod m;` binds only `m` here; its items live in another file and
        // are not in this module's scope. An INLINE module's items are reached
        // by the visitor, not by recursing here.
        syn::Item::Mod(it) => inert_attrs(&it.attrs, names, false),
        // A `macro_rules!` DEFINITION binds a macro name and no type name. An
        // item-position macro INVOCATION (`d!();`, `d!{}`, `d![]`,
        // `include!(..)`) parses as the same variant with `ident: None`, and
        // its expansion — which this module cannot see — really does rebind
        // type names file-wide (MEASURED).
        syn::Item::Macro(it) => it.ident.is_some() && inert_attrs(&it.attrs, names, false),
        // `extern crate m as core;` at a crate root rebinds the EXTERN PRELUDE,
        // so even `::core::primitive::u64` stops denoting the primitive
        // (MEASURED: `lead_bytes=4`). Everything else — `ForeignMod`,
        // `Verbatim`, and any variant `syn` grows later — is unmodelled by
        // construction.
        _ => false,
    }
}

fn inert_attrs(attrs: &[syn::Attribute], names: &FileTypeNames, inner: bool) -> bool {
    attrs.iter().all(|attr| inert_attr(attr, names, inner))
}

fn inert_attr(attr: &syn::Attribute, names: &FileTypeNames, inner: bool) -> bool {
    let path = attr.path();
    if path.leading_colon.is_some() {
        return false;
    }
    let segments: Vec<String> = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect();
    match segments.len() {
        1 => {
            let name = segments[0].as_str();
            if name == "derive" {
                return derive_list_is_builtin(attr, names);
            }
            INERT_BUILTIN_ATTRS.contains(&name) || (inner && INERT_INNER_ATTRS.contains(&name))
        }
        2 => INERT_ATTR_NAMESPACES.contains(&segments[0].as_str()) && !names.binds(&segments[0]),
        _ => false,
    }
}

/// True when every path inside `#[derive(..)]` names one of the nine built-in
/// derives AND the file binds none of those names (a `use m::Clone;` makes
/// `#[derive(Clone)]` resolve to a third-party macro again).
fn derive_list_is_builtin(attr: &syn::Attribute, names: &FileTypeNames) -> bool {
    let mut all_builtin = true;
    let parsed = attr.parse_nested_meta(|meta| {
        let Some(ident) = meta.path.get_ident() else {
            all_builtin = false;
            return Ok(());
        };
        let name = ident.to_string();
        if !BUILTIN_DERIVES.contains(&name.as_str()) || names.binds(&name) {
            all_builtin = false;
        }
        Ok(())
    });
    parsed.is_ok() && all_builtin
}

/// The syntactic width map of `ty`, read against the file's own type names.
pub(crate) fn shape_of(ty: &Type, names: &FileTypeNames) -> Wid {
    if !names.enumerable {
        return shape_of_unenumerable(ty);
    }
    shape_of_inner(ty, names, 0, &mut BTreeSet::new())
}

/// THE LANE-OFF MAP. The file holds a construct whose bindings its text cannot
/// enumerate, so no name in it can be resolved — including the primitive
/// spellings, which a macro expansion, an `extern crate` or a glob can all
/// rebind (MEASURED; see the module header).
///
/// Every answer is [`Wid::Opaque`] or [`Wid::Neutral`]: carry nothing, refuse
/// nothing. The `Some(suffix)` payload is produced on EXACTLY the shape HEAD's
/// two bare-scalar recorders accepted — a single-segment, leading-colon-free,
/// argument-free primitive name — so `scalar_int_suffix` reproduces HEAD
/// byte-for-byte here and composites reach the walk with no width to drop.
fn shape_of_unenumerable(ty: &Type) -> Wid {
    let Type::Path(type_path) = ty else {
        return Wid::Opaque(None);
    };
    if type_path.qself.is_some()
        || type_path.path.leading_colon.is_some()
        || type_path.path.segments.len() != 1
    {
        return Wid::Opaque(None);
    }
    let segment = &type_path.path.segments[0];
    if !matches!(segment.arguments, syn::PathArguments::None) {
        return Wid::Opaque(None);
    }
    match primitive_leaf(&segment.ident.to_string()) {
        Some(Wid::Scalar(suffix)) => Wid::Opaque(Some(suffix)),
        Some(Wid::DefaultInt) => Wid::Opaque(Some("i32")),
        Some(Wid::Neutral) => Wid::Neutral,
        _ => Wid::Opaque(None),
    }
}

fn shape_of_inner(
    ty: &Type,
    names: &FileTypeNames,
    depth: usize,
    visiting: &mut BTreeSet<String>,
) -> Wid {
    if depth > 8 {
        return Wid::Undecided;
    }
    match ty {
        Type::Paren(paren) => shape_of_inner(&paren.elem, names, depth + 1, visiting),
        Type::Group(group) => shape_of_inner(&group.elem, names, depth + 1, visiting),
        Type::Reference(reference) => Wid::Ref(Box::new(shape_of_inner(
            &reference.elem,
            names,
            depth + 1,
            visiting,
        ))),
        Type::Array(array) => Wid::Seq(Box::new(shape_of_inner(
            &array.elem,
            names,
            depth + 1,
            visiting,
        ))),
        Type::Slice(slice) => Wid::Seq(Box::new(shape_of_inner(
            &slice.elem,
            names,
            depth + 1,
            visiting,
        ))),
        Type::Tuple(tuple) => {
            if tuple.elems.is_empty() {
                return Wid::Neutral;
            }
            Wid::Tuple(
                tuple
                    .elems
                    .iter()
                    .map(|elem| shape_of_inner(elem, names, depth + 1, visiting))
                    .collect(),
            )
        }
        Type::Path(type_path) => {
            if type_path.qself.is_some() {
                return Wid::Undecided;
            }
            let segments: Vec<&syn::PathSegment> = type_path.path.segments.iter().collect();
            let Some(last) = segments.last() else {
                return Wid::Undecided;
            };
            let last_name = last.ident.to_string();
            // `Option<T>` / `Vec<T>`, bare or through the std paths.
            if matches!(last_name.as_str(), "Option" | "Vec") {
                let prefix: Vec<String> = segments[..segments.len() - 1]
                    .iter()
                    .map(|segment| segment.ident.to_string())
                    .collect();
                // A qualified `std::vec::Vec` is only the std one when nothing
                // rebinds its FIRST segment: `mod std { … }` / `use m as std;`
                // / a fn-body `use m as std;` all capture it. A leading `::`
                // names the crate and cannot be captured.
                let root_intact =
                    |root: &str| type_path.path.leading_colon.is_some() || !names.binds(root);
                let prefix_ok = match (last_name.as_str(), prefix.len()) {
                    (_, 0) => type_path.path.leading_colon.is_none() && !names.binds(&last_name),
                    ("Option", 2) => {
                        matches!(prefix[0].as_str(), "std" | "core")
                            && prefix[1] == "option"
                            && root_intact(&prefix[0])
                    }
                    ("Vec", 2) => {
                        matches!(prefix[0].as_str(), "std" | "alloc")
                            && prefix[1] == "vec"
                            && root_intact(&prefix[0])
                    }
                    _ => false,
                };
                if !prefix_ok {
                    return Wid::Undecided;
                }
                if segments[..segments.len() - 1]
                    .iter()
                    .any(|segment| !matches!(segment.arguments, syn::PathArguments::None))
                {
                    return Wid::Undecided;
                }
                let syn::PathArguments::AngleBracketed(args) = &last.arguments else {
                    return Wid::Undecided;
                };
                if args.args.len() != 1 {
                    return Wid::Undecided;
                }
                let syn::GenericArgument::Type(inner) = &args.args[0] else {
                    return Wid::Undecided;
                };
                let inner = shape_of_inner(inner, names, depth + 1, visiting);
                return if last_name == "Option" {
                    Wid::Opt(Box::new(inner))
                } else {
                    Wid::Vector(Box::new(inner))
                };
            }
            // `core::primitive::u8` / `std::primitive::u8`.
            if segments.len() == 3
                && matches!(segments[0].ident.to_string().as_str(), "core" | "std")
                && segments[1].ident == "primitive"
                && segments[..2]
                    .iter()
                    .all(|segment| matches!(segment.arguments, syn::PathArguments::None))
                && matches!(last.arguments, syn::PathArguments::None)
            {
                let leaf = primitive_leaf(&last_name);
                // `::core::primitive::u8` names the CRATE `core`. A leading
                // `::` path resolves to an external crate and nothing in the
                // file — a `mod core`, a `use m as core;`, a body-scope import
                // or a glob — can capture it. THIS is the glob-proof spelling
                // (measured: in a file whose glob rebinds `core`,
                // `core::primitive::u8` is eight bytes and
                // `::core::primitive::u8` is one).
                if type_path.path.leading_colon.is_some() {
                    return leaf.unwrap_or(Wid::Undecided);
                }
                // Unqualified, the first segment is an ordinary name. A file
                // item, an import, an inline `mod` or a body-scope `use` that
                // binds `core` / `std` redirects the whole path: `mod core {
                // pub mod primitive { pub type u64 = u32; } }` and `use m as
                // core;` were both measured as false `Verified`s whose twins
                // panic at `elem_size=4`.
                if names.binds(&segments[0].ident.to_string()) {
                    return Wid::Undecided;
                }
                // A glob can bind `core` too — and it does not reach here,
                // because a glob makes the whole file unenumerable and
                // `shape_of` never descends. See `enumerable`.
                return leaf.unwrap_or(Wid::Undecided);
            }
            if segments.len() != 1 || !matches!(last.arguments, syn::PathArguments::None) {
                return Wid::Undecided;
            }
            // A name an INLINE `mod` of this file also binds cannot be decided
            // in either direction: the table is file-scope and the extraction
            // is handed no module path, so a function inside that module must
            // not read the file-scope meaning, and a function outside it must
            // not read the module's. REFUSE rather than guess.
            if names.nested_bound_names.contains(&last_name) {
                return Wid::Undecided;
            }
            // A name the file BINDS is not the primitive it spells. `type u64 =
            // u8; let x: u64 = 200;` was a live false `Verified`; it now
            // resolves through the alias, or refuses.
            if names.declared_names.contains(&last_name) {
                // ... but only for a file with NO inline module. A submodule
                // does not inherit the file's items and this table carries no
                // module path, so a file-scope alias read for a function that
                // may live inside `mod inner` is a guess — and it was measured
                // as a false `Verified`. See `has_inline_mod`.
                if names.has_inline_mod {
                    return Wid::Undecided;
                }
                let Some(target) = names.aliases.get(&last_name) else {
                    return Wid::Undecided;
                };
                if !visiting.insert(last_name.clone()) {
                    return Wid::Undecided;
                }
                let resolved = shape_of_inner(target, names, depth + 1, visiting);
                visiting.remove(&last_name);
                return resolved;
            }
            if names.imported_names.contains(&last_name) {
                // An IMPORT that spells a width-free primitive (`int`, `nat`,
                // `bool`, `char`, `f32`, `f64`) is still read as that
                // primitive: a width-free leaf renders UNCHANGED, so this can
                // never attach a wrong width — it only declines to refuse. An
                // import that spells a width-BEARING primitive (`use foo::u8;`)
                // stays `Undecided` and a spine literal under it refuses.
                return match primitive_leaf(&last_name) {
                    Some(Wid::Neutral) => Wid::Neutral,
                    _ => Wid::Undecided,
                };
            }
            // Nothing this file holds binds the name, and the file is
            // ENUMERABLE — so its text really does say that. A glob, an
            // item-position macro invocation or an `extern crate` could each
            // rebind it, and each of those makes the file unenumerable before
            // `shape_of` descends here at all.
            primitive_leaf(&last_name).unwrap_or(Wid::Undecided)
        }
        _ => Wid::Undecided,
    }
}

/// The verbatim integer suffix of a `let`/parameter type annotation, when that
/// annotation DENOTES a primitive integer type in this file. The single leaf
/// classifier behind `single_typed_bindings` and
/// `body_extract::local_pat_declared_int_suffix`.
///
/// With no file table this falls back to the bare, unshadowed spelling, which
/// is exactly what both recorders did before (their behaviour is preserved
/// byte-for-byte when the source file is unknown). The stand-in table is the
/// DEFAULT one, whose `enumerable` is false — a file nobody looked at is
/// exactly the case the closed world refuses to speak for, and the lane-off map
/// it produces is HEAD's behaviour by construction.
pub(crate) fn scalar_int_suffix(ty: &Type, names: Option<&FileTypeNames>) -> Option<&'static str> {
    let shape = match names {
        Some(names) => shape_of(ty, names),
        None => {
            let empty = FileTypeNames::default();
            shape_of(ty, &empty)
        }
    };
    match shape {
        Wid::Scalar(suffix) => Some(suffix),
        // An UNENUMERABLE file keeps the BARE SCALAR recorders exactly as they
        // were before this lane existed — `Opaque` carries a suffix on exactly
        // the spelling HEAD accepted, and `None` on every other. Their
        // blindness to an unenumerable file is pre-existing and is left
        // recorded open; what this lane must not do is extend it into composite
        // positions, which is why the WALK treats `Opaque` as "carry nothing"
        // while this classifier does not.
        Wid::Opaque(suffix) => suffix,
        Wid::DefaultInt => Some("i32"),
        _ => None,
    }
}

/// Outcome of [`render_with_declared_width`].
#[derive(Clone, Debug, Default)]
pub(crate) struct WalkOutcome {
    /// The re-spelled initializer — `Some` ONLY when the walk rendered the
    /// whole expression AND actually attached at least one suffix the source
    /// did not carry. A walk that would merely re-print the same value returns
    /// `None`, so HEAD's text is preserved BYTE-FOR-BYTE wherever no width is
    /// being carried (this is what keeps `0xffff_ffffu32` from being
    /// normalised to `4294967295u32`, `[a , b]` from losing its spacing, and
    /// `let x: Option<u32> = None;` from preempting the typed
    /// `scoped_option_none_value` rendering — all three measured on the corpus
    /// A/B before the flag existed).
    pub(crate) rendered: Option<String>,
    /// True when the walk produced a rendering for every node of the
    /// expression, whether or not anything was carried. The Option payload
    /// lane's H1b scan reads this, not `rendered`.
    pub(crate) complete: bool,
    /// True when every numeric literal the expression holds sits at a position
    /// the ascription DECIDES and models correctly. The Option payload lane's
    /// whole-body H1b scan skips an initializer only when this is set.
    pub(crate) all_decided: bool,
}

/// Descend `shape` and `expr` together over the admitted constructor spine,
/// re-spelling bare integer literals at the width the shape declares.
///
/// `Ok(outcome)` with `rendered = Some(..)` is the carry; with `rendered =
/// None` the caller keeps today's rendering. `Err` is a fail-closed refusal
/// (R2a-e) — the caller sets `parse_error` and the whole extraction stops.
pub(crate) fn render_with_declared_width(
    shape: &Wid,
    expr: &Expr,
    names: &FileTypeNames,
    ascribed: &Type,
) -> Result<WalkOutcome, TrustVcError> {
    let mut walk = Walk {
        names,
        ascribed,
        all_decided: true,
        carried: false,
    };
    let rendered = walk.node(shape, expr)?;
    let complete = rendered.is_some();
    Ok(WalkOutcome {
        rendered: if walk.carried { rendered } else { None },
        complete,
        all_decided: walk.all_decided,
    })
}

struct Walk<'a> {
    names: &'a FileTypeNames,
    ascribed: &'a Type,
    all_decided: bool,
    carried: bool,
}

impl Walk<'_> {
    fn refuse(&self, arm: &'static str, expr: &Expr) -> TrustVcError {
        refusal(arm, self.ascribed, expr)
    }

    /// `Ok(Some(text))` renders; `Ok(None)` means "this node is not renderable
    /// here, and no width is being dropped by leaving it alone".
    fn node(&mut self, shape: &Wid, expr: &Expr) -> Result<Option<String>, TrustVcError> {
        match expr {
            Expr::Paren(paren) => Ok(self.node(shape, &paren.expr)?.map(|it| format!("({it})"))),
            Expr::Group(group) => self.node(shape, &group.expr),
            Expr::Lit(lit) => self.literal(shape, expr, lit, false),
            Expr::Unary(syn::ExprUnary {
                op: syn::UnOp::Neg(_),
                expr: inner,
                ..
            }) if matches!(peel(inner), Expr::Lit(_)) => {
                let Expr::Lit(lit) = peel(inner) else {
                    unreachable!("guarded above")
                };
                self.literal(shape, expr, lit, true)
            }
            // CONSTANT INTEGER ARITHMETIC at a decided integer leaf. Every leaf
            // of the expression is an integer literal, so no user `Add` impl can
            // apply and rustc's inference has exactly one choice: the position's
            // type propagates to every operand. `let x: Option<u8> = Some(100 +
            // 50);` is a TRUE claim that HEAD verified, and walling it off
            // would trade a false `Verified` this lane never had for a lost
            // one it did. See `is_int_const_expr` for the closure of the rule.
            Expr::Unary(syn::ExprUnary {
                op, expr: inner, ..
            }) if matches!(op, syn::UnOp::Neg(_) | syn::UnOp::Not(_))
                && matches!(shape, Wid::Scalar(_) | Wid::DefaultInt)
                && is_int_const_expr(expr) =>
            {
                match self.node(shape, inner)? {
                    Some(text) => Ok(Some(format!("{}{text}", op.to_token_stream()))),
                    None => self.unrenderable(shape, expr),
                }
            }
            Expr::Binary(binary)
                if matches!(shape, Wid::Scalar(_) | Wid::DefaultInt) && is_int_const_expr(expr) =>
            {
                let op = binary.op.to_token_stream();
                if is_shift_op(&binary.op) {
                    // A SHIFT's right operand is typed INDEPENDENTLY of the
                    // result (`1u8 << 3` has an `i32` shift count), so it must
                    // never take the position's suffix.
                    return match self.node(shape, &binary.left)? {
                        Some(left) => Ok(Some(format!(
                            "{left} {op} {}",
                            binary.right.to_token_stream()
                        ))),
                        None => self.unrenderable(shape, expr),
                    };
                }
                let (Some(left), Some(right)) = (
                    self.node(shape, &binary.left)?,
                    self.node(shape, &binary.right)?,
                ) else {
                    return self.unrenderable(shape, expr);
                };
                Ok(Some(format!("{left} {op} {right}")))
            }
            Expr::Unary(syn::ExprUnary {
                op: syn::UnOp::Neg(_),
                ..
            }) => self.off_spine(shape, expr),
            Expr::Tuple(tuple) => {
                let Wid::Tuple(elem_shapes) = shape else {
                    return self.off_spine(shape, expr);
                };
                if elem_shapes.len() != tuple.elems.len() {
                    // The initializer cannot have this type; refuse rather than
                    // place literals by guesswork.
                    if shape.holds_width() {
                        return Err(self.refuse(ERR_ARITY, expr));
                    }
                    return self.off_spine(shape, expr);
                }
                let mut parts = Vec::with_capacity(tuple.elems.len());
                for (elem_shape, elem) in elem_shapes.iter().zip(tuple.elems.iter()) {
                    match self.node(elem_shape, elem)? {
                        Some(text) => parts.push(text),
                        None => return self.unrenderable(shape, expr),
                    }
                }
                let trailing = if parts.len() == 1 { "," } else { "" };
                Ok(Some(format!("({}{trailing})", parts.join(", "))))
            }
            Expr::Array(array) => {
                let Wid::Seq(elem_shape) = shape else {
                    if shape.holds_width() {
                        return Err(self.refuse(ERR_ARITY, expr));
                    }
                    return self.off_spine(shape, expr);
                };
                let mut parts = Vec::with_capacity(array.elems.len());
                for elem in &array.elems {
                    match self.node(elem_shape, elem)? {
                        Some(text) => parts.push(text),
                        None => return self.unrenderable(shape, expr),
                    }
                }
                Ok(Some(format!("[{}]", parts.join(", "))))
            }
            Expr::Repeat(repeat) => {
                let Wid::Seq(elem_shape) = shape else {
                    if shape.holds_width() {
                        return Err(self.refuse(ERR_ARITY, expr));
                    }
                    return self.off_spine(shape, expr);
                };
                let Some(value) = self.node(elem_shape, &repeat.expr)? else {
                    return self.unrenderable(shape, expr);
                };
                // The LENGTH is `usize`-decided by rustc and must NEVER take the
                // element suffix.
                Ok(Some(format!("[{value}; {}]", repeat.len.to_token_stream())))
            }
            Expr::Reference(reference) => {
                let Wid::Ref(inner_shape) = shape else {
                    return self.off_spine(shape, expr);
                };
                let Some(inner) = self.node(inner_shape, &reference.expr)? else {
                    return self.unrenderable(shape, expr);
                };
                let mutability = if reference.mutability.is_some() {
                    "mut "
                } else {
                    ""
                };
                Ok(Some(format!("&{mutability}{inner}")))
            }
            Expr::Call(call) => {
                let Wid::Opt(payload_shape) = shape else {
                    return self.off_spine(shape, expr);
                };
                if !is_plain_path(&call.func, "Some") || call.args.len() != 1 {
                    return self.off_spine(shape, expr);
                }
                if self.names.binds("Some") || self.names.binds("Option") {
                    if shape.holds_width() && tokens_hold_bare_int_literal(expr) {
                        return Err(self.refuse(ERR_SHADOWED_CTOR, expr));
                    }
                    return self.unrenderable(shape, expr);
                }
                let Some(payload) = self.node(payload_shape, &call.args[0])? else {
                    return self.unrenderable(shape, expr);
                };
                Ok(Some(format!("Some({payload})")))
            }
            Expr::Path(path) => {
                if matches!(shape, Wid::Opt(_)) && is_plain_path_expr(path, "None") {
                    if self.names.binds("None") || self.names.binds("Option") {
                        return self.unrenderable(shape, expr);
                    }
                    return Ok(Some("None".to_string()));
                }
                self.off_spine(shape, expr)
            }
            Expr::Macro(mac) => {
                let is_vec = mac
                    .mac
                    .path
                    .get_ident()
                    .is_some_and(|ident| *ident == "vec")
                    && mac.mac.path.leading_colon.is_none();
                if !is_vec {
                    return self.off_spine(shape, expr);
                }
                let Wid::Vector(elem_shape) = shape else {
                    if shape.holds_width() && tokens_hold_bare_int_literal(expr) {
                        return Err(self.refuse(ERR_ARITY, expr));
                    }
                    return self.off_spine(shape, expr);
                };
                if self.names.binds("vec") || self.names.binds("Vec") {
                    if shape.holds_width() && tokens_hold_bare_int_literal(expr) {
                        return Err(self.refuse(ERR_SHADOWED_CTOR, expr));
                    }
                    return self.unrenderable(shape, expr);
                }
                // `vec![a, b]` and `vec![v; n]`. The repeat body is `v; n`
                // WITHOUT brackets, so it is not a `syn::ExprRepeat`; parse the
                // two halves directly.
                let repeat = mac.mac.parse_body_with(|input: syn::parse::ParseStream| {
                    let value: Expr = input.parse()?;
                    input.parse::<syn::Token![;]>()?;
                    let len: Expr = input.parse()?;
                    Ok((value, len))
                });
                if let Ok((value_expr, len_expr)) = repeat {
                    let Some(value) = self.node(elem_shape, &value_expr)? else {
                        return self.unrenderable(shape, expr);
                    };
                    // The LENGTH is `usize`-decided by rustc and must NEVER take
                    // the element suffix.
                    return Ok(Some(format!(
                        "vec![{value}; {}]",
                        len_expr.to_token_stream()
                    )));
                }
                let Ok(elems) = mac.mac.parse_body_with(
                    syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated,
                ) else {
                    return self.unrenderable(shape, expr);
                };
                let mut parts = Vec::with_capacity(elems.len());
                for elem in &elems {
                    match self.node(elem_shape, elem)? {
                        Some(text) => parts.push(text),
                        None => return self.unrenderable(shape, expr),
                    }
                }
                Ok(Some(format!("vec![{}]", parts.join(", "))))
            }
            _ => self.off_spine(shape, expr),
        }
    }

    /// An integer or float literal at `shape`.
    fn literal(
        &mut self,
        shape: &Wid,
        whole: &Expr,
        lit: &syn::ExprLit,
        negated: bool,
    ) -> Result<Option<String>, TrustVcError> {
        match &lit.lit {
            syn::Lit::Int(int) => {
                let digits = int.base10_digits().to_string();
                let sign = if negated { "-" } else { "" };
                if !int.suffix().is_empty() {
                    // A source suffix already carries the width. If it
                    // CONTRADICTS the annotation the program is a type error;
                    // never silently re-spell it.
                    if let Wid::Scalar(declared) = shape {
                        if int.suffix() != *declared {
                            return Err(self.refuse(ERR_ARITY, whole));
                        }
                    }
                    if matches!(shape, Wid::DefaultInt) && int.suffix() != "i32" {
                        return Err(self.refuse(ERR_ARITY, whole));
                    }
                    return Ok(Some(format!("{sign}{digits}{}", int.suffix())));
                }
                match shape {
                    Wid::Scalar(declared) => {
                        if !literal_fits(&digits, negated, declared) {
                            return Err(self.refuse(ERR_RANGE, whole));
                        }
                        self.carried = true;
                        Ok(Some(format!("{sign}{digits}{declared}")))
                    }
                    // Already the rendering default: decided, nothing to carry.
                    Wid::DefaultInt => Ok(Some(format!("{sign}{digits}"))),
                    // A glob-bearing file: the name may not be the primitive it
                    // spells, so neither carry nor refuse — HEAD's rendering,
                    // and never counted decided.
                    Wid::Opaque(_) => {
                        self.all_decided = false;
                        Ok(None)
                    }
                    Wid::Undecided => Err(self.refuse(ERR_UNDECIDED, whole)),
                    // An integer literal cannot have a float / bool / char type;
                    // leave today's rendering and do not claim decidedness.
                    _ => {
                        self.all_decided = false;
                        Ok(None)
                    }
                }
            }
            syn::Lit::Float(float) => {
                // Floats are never carried (module header): render unchanged,
                // and never count as decided unless the source already suffixed
                // them.
                if float.suffix().is_empty() {
                    self.all_decided = false;
                }
                let sign = if negated { "-" } else { "" };
                Ok(Some(format!("{sign}{}", float.to_token_stream())))
            }
            syn::Lit::Bool(_) | syn::Lit::Char(_) | syn::Lit::Str(_) if !negated => {
                Ok(Some(lit.to_token_stream().to_string()))
            }
            _ => self.unrenderable(shape, whole),
        }
    }

    /// An expression that is not on the admitted spine. R2(b): refuse when a
    /// bare integer literal sits inside it at a WIDTH-BEARING position — there
    /// we KNOW a width would be dropped. Otherwise leave today's rendering.
    ///
    /// DELIBERATELY NOT refused here: a bare literal under an `Undecided`
    /// shape that is NOT on the spine (a struct literal, a user constructor
    /// call, `MyType::from(1)`). R2(a) is scoped to SPINE-reached literals
    /// precisely so those keep today's handling: they are separate,
    /// already-recorded holes that fail closed downstream, and widening into
    /// them would convert currently-safe verdicts into refusals for no
    /// soundness gain.
    fn off_spine(&mut self, shape: &Wid, expr: &Expr) -> Result<Option<String>, TrustVcError> {
        if shape.holds_width() && tokens_hold_bare_int_literal(expr) {
            return Err(self.refuse(ERR_WALL, expr));
        }
        self.unrenderable(shape, expr)
    }

    /// The node cannot be rendered by this walk, and nothing about it says a
    /// width is being dropped. Today's rendering stands.
    fn unrenderable(&mut self, _shape: &Wid, expr: &Expr) -> Result<Option<String>, TrustVcError> {
        if tokens_hold_bare_numeric_literal(expr) {
            self.all_decided = false;
        }
        Ok(None)
    }
}

fn is_shift_op(op: &syn::BinOp) -> bool {
    matches!(op, syn::BinOp::Shl(_) | syn::BinOp::Shr(_))
}

/// True when every leaf of `expr` is an INTEGER literal and every node is an
/// operator whose integer impl is the primitive one.
///
/// This is the whole soundness condition for descending into arithmetic. A
/// position typed `u8` makes `100 + 50` unify at `u8`, so both literals are
/// `u8` — but only because no operand can be a user type: `impl Add<i64> for
/// MyT { type Output = u8; }` would give a `u8`-typed sum one of whose operands
/// is an `i64` literal. Requiring every leaf to be an integer literal rules
/// that out, because a literal can only take a primitive integer type.
///
/// Non-literal operands are deliberately NOT admitted even though inference
/// would propagate the same way for the built-in impls — `Some(z + 50)` cannot
/// be shown to use them from this file alone.
fn is_int_const_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Paren(paren) => is_int_const_expr(&paren.expr),
        Expr::Group(group) => is_int_const_expr(&group.expr),
        Expr::Lit(lit) => matches!(lit.lit, syn::Lit::Int(_)),
        Expr::Unary(unary) => {
            matches!(unary.op, syn::UnOp::Neg(_) | syn::UnOp::Not(_))
                && is_int_const_expr(&unary.expr)
        }
        Expr::Binary(binary) => {
            matches!(
                binary.op,
                syn::BinOp::Add(_)
                    | syn::BinOp::Sub(_)
                    | syn::BinOp::Mul(_)
                    | syn::BinOp::Div(_)
                    | syn::BinOp::Rem(_)
                    | syn::BinOp::BitAnd(_)
                    | syn::BinOp::BitOr(_)
                    | syn::BinOp::BitXor(_)
                    | syn::BinOp::Shl(_)
                    | syn::BinOp::Shr(_)
            ) && is_int_const_expr(&binary.left)
                && is_int_const_expr(&binary.right)
        }
        _ => false,
    }
}

fn peel(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(paren) => peel(&paren.expr),
        Expr::Group(group) => peel(&group.expr),
        other => other,
    }
}

fn is_plain_path(expr: &Expr, name: &str) -> bool {
    match peel(expr) {
        Expr::Path(path) => is_plain_path_expr(path, name),
        _ => false,
    }
}

fn is_plain_path_expr(path: &syn::ExprPath, name: &str) -> bool {
    path.qself.is_none()
        && path.path.leading_colon.is_none()
        && path.path.segments.len() == 1
        && path.path.segments[0].ident == name
        && matches!(path.path.segments[0].arguments, syn::PathArguments::None)
}

/// True when `expr` syntactically holds a bare (unsuffixed) INTEGER literal
/// that could take a width from its position.
///
/// Deliberately syn-aware rather than token-level: a tuple-field index (`x.0`)
/// and an index expression (`a[i + 1]`) are `usize`-decided by the language,
/// not value literals whose width an annotation could fix. A raw token scan
/// counted `x.0` and turned `let r: &mut u64 = x.0;` into a refusal (measured
/// on the corpus A/B, `mut_refs_closures.rs`).
fn tokens_hold_bare_int_literal(expr: &Expr) -> bool {
    holds_bare_literal(expr, false)
}

fn tokens_hold_bare_numeric_literal(expr: &Expr) -> bool {
    holds_bare_literal(expr, true)
}

fn holds_bare_literal(expr: &Expr, floats_too: bool) -> bool {
    use syn::visit::Visit;
    struct Finder {
        floats_too: bool,
        found: bool,
    }
    impl<'ast> Visit<'ast> for Finder {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            match expr {
                // The member of `x.0` is a field selector, not a value.
                Expr::Field(field) => self.visit_expr(&field.base),
                // `a[i]`'s index is `usize`-decided by the `Index` impl.
                Expr::Index(index) => self.visit_expr(&index.expr),
                other => syn::visit::visit_expr(self, other),
            }
        }
        fn visit_lit(&mut self, lit: &'ast syn::Lit) {
            match lit {
                syn::Lit::Int(int) if int.suffix().is_empty() => self.found = true,
                syn::Lit::Float(float) if self.floats_too && float.suffix().is_empty() => {
                    self.found = true
                }
                _ => {}
            }
        }
        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            if tokens_hold(mac.tokens.clone(), self.floats_too) {
                self.found = true;
            }
        }
    }
    let mut finder = Finder {
        floats_too,
        found: false,
    };
    finder.visit_expr(expr);
    finder.found
}

fn tokens_hold(tokens: proc_macro2::TokenStream, floats_too: bool) -> bool {
    tokens.into_iter().any(|tree| match tree {
        proc_macro2::TokenTree::Literal(literal) => {
            let tokens = literal.into_token_stream();
            syn::parse2::<syn::LitInt>(tokens.clone()).is_ok_and(|int| int.suffix().is_empty())
                || (floats_too
                    && syn::parse2::<syn::LitFloat>(tokens)
                        .is_ok_and(|float| float.suffix().is_empty()))
        }
        proc_macro2::TokenTree::Group(group) => tokens_hold(group.stream(), floats_too),
        _ => false,
    })
}

/// Sign-aware range check. `-128` at `i8` passes and `128` at `i8` does not; a
/// negative literal at ANY unsigned leaf always fails (the rule
/// `typed_default_int_literal_value` already spelled as
/// `digits.starts_with('-') && suffix.starts_with('u')`).
///
/// `usize` / `isize` are DELIBERATELY exempt: their width is directive-
/// controlled and only `crate::ir::pointer_width()` knows it at lowering time,
/// so the encoder keeps that job.
pub(crate) fn literal_fits(digits: &str, negated: bool, suffix: &str) -> bool {
    if matches!(suffix, "usize" | "isize") {
        return true;
    }
    let Ok(magnitude) = digits.parse::<u128>() else {
        return false;
    };
    let Some(bits) = suffix
        .strip_prefix('u')
        .or_else(|| suffix.strip_prefix('i'))
        .and_then(|width| width.parse::<u32>().ok())
    else {
        return false;
    };
    if bits == 0 || bits > 128 {
        return false;
    }
    if suffix.starts_with('u') {
        if negated {
            return magnitude == 0;
        }
        return bits >= 128 || magnitude < (1u128 << bits);
    }
    let half = 1u128 << (bits - 1);
    if negated {
        magnitude <= half
    } else {
        magnitude < half
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names_of(src: &str) -> FileTypeNames {
        FileTypeNames::from_file(&syn::parse_file(src).expect("parse"))
    }

    fn shape(src: &str, ty: &str) -> Wid {
        shape_of(&syn::parse_str::<Type>(ty).expect("type"), &names_of(src))
    }

    #[test]
    fn bare_primitive_names_classify() {
        assert_eq!(shape("", "u8"), Wid::Scalar("u8"));
        assert_eq!(shape("", "i32"), Wid::DefaultInt);
        assert_eq!(shape("", "f32"), Wid::Neutral);
        assert_eq!(shape("", "usize"), Wid::Scalar("usize"));
        assert_eq!(shape("", "core::primitive::u8"), Wid::Scalar("u8"));
        assert_eq!(shape("", "::core::primitive::u8"), Wid::Scalar("u8"));
    }

    #[test]
    fn containers_classify() {
        assert_eq!(
            shape("", "Option<u8>"),
            Wid::Opt(Box::new(Wid::Scalar("u8")))
        );
        assert_eq!(
            shape("", "Vec<u8>"),
            Wid::Vector(Box::new(Wid::Scalar("u8")))
        );
        assert_eq!(
            shape("", "std::vec::Vec<u8>"),
            Wid::Vector(Box::new(Wid::Scalar("u8")))
        );
        assert_eq!(shape("", "[u8; 3]"), Wid::Seq(Box::new(Wid::Scalar("u8"))));
        assert_eq!(
            shape("", "&[u8]"),
            Wid::Ref(Box::new(Wid::Seq(Box::new(Wid::Scalar("u8")))))
        );
        assert_eq!(
            shape("", "(u8, u16)"),
            Wid::Tuple(vec![Wid::Scalar("u8"), Wid::Scalar("u16")])
        );
        assert_eq!(shape("", "HashMap<u8, u8>"), Wid::Undecided);
        assert_eq!(shape("", "Box<u8>"), Wid::Undecided);
        assert_eq!(shape("", "impl Copy"), Wid::Undecided);
    }

    #[test]
    fn aliases_resolve_and_cycles_refuse() {
        assert_eq!(shape("type Byte = u8;", "Byte"), Wid::Scalar("u8"));
        assert_eq!(
            shape("type Bytes = Vec<u8>;", "Bytes"),
            Wid::Vector(Box::new(Wid::Scalar("u8")))
        );
        assert_eq!(shape("type A = B; type B = A;", "A"), Wid::Undecided);
        assert_eq!(shape("type G<T> = Vec<T>;", "G<u8>"), Wid::Undecided);
    }

    #[test]
    fn a_file_bound_name_is_not_the_primitive_it_spells() {
        // The live false `Verified` this closes.
        assert_eq!(shape("type u64 = u8;", "u64"), Wid::Scalar("u8"));
        assert_eq!(shape("struct u8;", "u8"), Wid::Undecided);
        assert_eq!(shape("use other::Byte;", "Byte"), Wid::Undecided);
    }

    #[test]
    fn a_cfg_bearing_file_is_unenumerable() {
        // `syn` does not evaluate `cfg`, so the file's text does not enumerate
        // its own items: the whole lane is off, primitives included.
        let src = "#[cfg(feature = \"x\")] type Byte = u8;";
        assert!(!names_of(src).enumerable);
        assert_eq!(shape(src, "Byte"), Wid::Opaque(None));
        assert_eq!(shape(src, "u8"), Wid::Opaque(Some("u8")));
        assert_eq!(shape(src, "Vec<u8>"), Wid::Opaque(None));
    }

    /// THE CLOSED WORLD. Each of these was measured as a false `Verified` (or
    /// a refuted TRUE claim) on the `fv3` lens pair before the admission
    /// existed; see the module header for the stock-rustc twins.
    #[test]
    fn an_unenumerable_construct_turns_the_whole_lane_off() {
        let off = |src: &str| {
            assert!(!names_of(src).enumerable, "must be unenumerable: {src}");
            // No carry ...
            assert!(render(src, "Vec<u8>", "vec![200]")
                .unwrap()
                .rendered
                .is_none());
            // ... and no refusal, on any spelling.
            assert!(render(src, "Vec<Byte>", "vec![200]").is_ok());
            assert!(render(src, "Byte", "200").is_ok());
        };
        // An item-position macro INVOCATION, in every spelling measured to
        // leak: `d!();`, `d!{}`, `d![]`, a macro that invokes another macro,
        // one that generates the `use m as core;` prefix capture, and one that
        // generates a `Vec` alias that reprojects the element.
        off("macro_rules! d { () => { type u64 = u8; } } d!();");
        off("macro_rules! d { () => { type u64 = u8; } } d!{}");
        off("macro_rules! d { () => { type u64 = u8; } } d![];");
        off("macro_rules! i { () => {}; } macro_rules! o { () => { i!(); }; } o!();");
        off("macro_rules! c { () => { use m as core; }; } c!();");
        off("macro_rules! v { () => { pub type Vec<T> = T; }; } v!();");
        off("include!(\"other.rs\");");
        // `extern crate m as core;` rebinds the EXTERN PRELUDE, so even
        // `::core::primitive::u64` stops denoting the primitive.
        off("extern crate self as core;");
        // A third-party derive and an unknown attribute macro both inject.
        off("#[derive(Serialize)] struct S;");
        off("#[my_attr] struct S;");
        // `#![no_implicit_prelude]` removes `Option` / `Some` / `Vec` / `vec!`.
        off("#![no_implicit_prelude]");
        // A glob, at file scope or in a body.
        off("use vstd::prelude::*;");
        off("fn f() { use vstd::prelude::*; }");
        // ... and an item written INSIDE a body reaches the same admission: a
        // `#[derive(Widen)] struct S;` there injects into that body's scope.
        off("fn f() { #[derive(Serialize)] struct S; }");
        off("fn f() { extern crate self as core; }");
        // THE BOUNDARY, stated as a test rather than only in prose: a macro in
        // STATEMENT position is not a `syn::Item`, so the admission does not
        // see it — and it does not need to. Its expansion binds only inside the
        // body that holds it, and for the function under extraction that is
        // already fail-closed by a different gate (measured: `let v: Vec<u8>`
        // after a body `shadow!();` returns `Unsupported shadow!() in
        // vc_extraction`, at BOTH lenses).
        assert!(names_of("fn f() { macro_rules! d { () => {}; } d!(); }").enumerable);
        // An unmodelled item kind.
        off("extern \"C\" { fn c(); }");
    }

    #[test]
    fn the_admitted_constructs_keep_carrying() {
        let on = |src: &str| assert!(names_of(src).enumerable, "must be enumerable: {src}");
        on("");
        on("type Byte = u8; struct S; enum E {} fn f() {} const K: u8 = 1;");
        on("use other::Byte; impl S { fn g() {} }");
        on("macro_rules! m { () => {}; }");
        on("#[allow(dead_code)] #[doc = \"x\"] #[inline] fn f() {}");
        // This workspace's own attribute macros, and the registered tool
        // namespaces, are inert by construction.
        on("#[trust_vc::ensures(true)] fn f() {}");
        on("#[rustfmt::skip] fn f() {}");
        // The nine built-in derives are specified to emit `impl` blocks only.
        on("#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default, PartialOrd, Ord)] struct S;");
        // ... unless the file rebinds the derive's NAME.
        assert!(!names_of("use m::Clone; #[derive(Clone)] struct S;").enumerable);
        // ... or borrows the namespace exemption.
        assert!(!names_of("use m as trust_vc; #[trust_vc::ensures(true)] fn f() {}").enumerable);
        // A file-scope carry still fires in an admitted file.
        assert_eq!(
            render("#[derive(Clone)] struct S;", "Vec<u8>", "vec![200]")
                .unwrap()
                .rendered
                .as_deref(),
            Some("vec![200u8]")
        );
    }

    #[test]
    fn an_inline_module_makes_every_file_declared_name_undecided() {
        // MEASURED false `Verified`: a function written INSIDE `mod inner` does
        // not see the file's items, and this table carries no module path.
        let src = "type u32 = ::core::primitive::u64; mod inner { pub fn f() {} }";
        assert!(
            names_of(src).enumerable,
            "an inline mod is still enumerable"
        );
        assert_eq!(shape(src, "u32"), Wid::Undecided);
        assert_eq!(
            shape(src, "Vec<u32>"),
            Wid::Vector(Box::new(Wid::Undecided))
        );
        // Primitives the file does not declare are unaffected in BOTH scopes.
        assert_eq!(shape(src, "u8"), Wid::Scalar("u8"));
        // With no inline module the alias resolves as before.
        assert_eq!(
            shape("type u32 = ::core::primitive::u64;", "u32"),
            Wid::Scalar("u64")
        );
    }

    #[test]
    fn sign_aware_bound_at_every_boundary() {
        assert!(literal_fits("255", false, "u8"));
        assert!(!literal_fits("256", false, "u8"));
        assert!(!literal_fits("1", true, "u8"));
        assert!(literal_fits("0", true, "u8"));
        assert!(literal_fits("127", false, "i8"));
        assert!(!literal_fits("128", false, "i8"));
        assert!(literal_fits("128", true, "i8"));
        assert!(!literal_fits("129", true, "i8"));
        let i128_half = 1u128 << 127;
        assert!(literal_fits(&(i128_half - 1).to_string(), false, "i128"));
        assert!(!literal_fits(&i128_half.to_string(), false, "i128"));
        assert!(literal_fits(&i128_half.to_string(), true, "i128"));
        assert!(!literal_fits(&(i128_half + 1).to_string(), true, "i128"));
        assert!(literal_fits(&u128::MAX.to_string(), false, "u128"));
        assert!(!literal_fits("1", true, "u128"));
        assert!(literal_fits("0", true, "u128"));
        // Production callers admit primitive widths only. Invalid direct
        // inputs still fail closed before either shift can overflow.
        for suffix in ["i0", "u0", "i129", "u129"] {
            assert!(!literal_fits("0", false, suffix));
        }
        // Directive-controlled widths are the encoder's job.
        assert!(literal_fits("99999999999999999999", false, "usize"));
        assert!(literal_fits("99999999999999999999", false, "isize"));
    }

    fn render(src: &str, ty: &str, init: &str) -> Result<WalkOutcome, TrustVcError> {
        let names = names_of(src);
        let ty = syn::parse_str::<Type>(ty).expect("type");
        let shape = shape_of(&ty, &names);
        let expr = syn::parse_str::<Expr>(init).expect("expr");
        render_with_declared_width(&shape, &expr, &names, &ty)
    }

    #[test]
    fn i128_option_initializer_boundaries_are_sign_aware() {
        let half = 1u128 << 127;
        for value in [(half - 1).to_string(), format!("-{half}")] {
            let init = format!("Some({value})");
            let expected = format!("Some({value}i128)");
            assert_eq!(
                render("", "Option<i128>", &init)
                    .expect("i128 max and min fit")
                    .rendered
                    .as_deref(),
                Some(expected.as_str())
            );
        }
        for value in [half.to_string(), format!("-{}", half + 1)] {
            let init = format!("Some({value})");
            let err = render("", "Option<i128>", &init)
                .expect_err("a value one past an i128 boundary must be refused");
            assert!(err.to_string().contains(ERR_RANGE), "{err}");
        }
    }

    #[test]
    fn the_ledger_hole_renders_the_spelling_that_already_works() {
        assert_eq!(
            render("", "Vec<u8>", "vec![200]")
                .unwrap()
                .rendered
                .as_deref(),
            Some("vec![200u8]")
        );
        assert_eq!(
            render("", "Option<u8>", "Some(200)")
                .unwrap()
                .rendered
                .as_deref(),
            Some("Some(200u8)")
        );
    }

    #[test]
    fn repeat_length_never_takes_the_element_suffix() {
        assert_eq!(
            render("", "[u8; 3]", "[200; 3]")
                .unwrap()
                .rendered
                .as_deref(),
            Some("[200u8; 3]")
        );
        assert_eq!(
            render("", "Vec<u8>", "vec![200; 3]")
                .unwrap()
                .rendered
                .as_deref(),
            Some("vec![200u8; 3]")
        );
    }

    #[test]
    fn negatives_tuples_and_refs_render() {
        assert_eq!(
            render("", "(i8, i8)", "(-128, 1)")
                .unwrap()
                .rendered
                .as_deref(),
            Some("(-128i8, 1i8)")
        );
        assert_eq!(
            render("", "&u8", "&200").unwrap().rendered.as_deref(),
            Some("&200u8")
        );
    }

    #[test]
    fn refusals_fire_on_their_own_arms() {
        let err = |r: Result<WalkOutcome, TrustVcError>| format!("{}", r.unwrap_err());
        assert!(err(render("use other::Byte;", "Byte", "200")).contains(ERR_UNDECIDED));
        // The wall's own domain is a NON-CONSTANT operand; constant integer
        // arithmetic is decided by the annotation and is carried (see
        // `constant_integer_arithmetic_is_decided_by_the_annotation`).
        assert!(err(render("", "Option<u8>", "Some(z + 50)")).contains(ERR_WALL));
        assert!(err(render("", "Vec<u8>", "vec![f(200)]")).contains(ERR_WALL));
        assert!(err(render("", "Option<u8>", "Some(300)")).contains(ERR_RANGE));
        assert!(err(render("", "(u8, u16)", "(1, 2, 3)")).contains(ERR_ARITY));
        assert!(err(render("", "Vec<u8>", "[200, 1]")).contains(ERR_ARITY));
        assert!(err(render(
            "fn Some(x: i64) -> Option<u8> { None }",
            "Option<u8>",
            "Some(200)"
        ))
        .contains(ERR_SHADOWED_CTOR));
    }

    #[test]
    fn nothing_is_claimed_where_no_width_is_dropped() {
        // No literal anywhere: today's rendering, no refusal.
        assert!(render("", "Vec<u8>", "other").unwrap().rendered.is_none());
        assert!(render("", "Vec<u8>", "f()").unwrap().rendered.is_none());
        assert!(render("", "Vec<u8>", "vec![a, b]")
            .unwrap()
            .rendered
            .is_none());
        // A user type with a struct-literal initializer keeps today's handling.
        assert!(render("struct S { a: u8 }", "S", "S { a: 1 }")
            .unwrap()
            .rendered
            .is_none());
    }

    #[test]
    fn a_nested_module_rebinding_is_undecided_in_both_directions() {
        // The table is FILE-scope and the extraction is handed no module path,
        // so neither the file-scope meaning nor the module's can be attached.
        let src = "type W = i64; mod inner { pub type W = i32; }";
        assert_eq!(shape(src, "W"), Wid::Undecided);
        assert_eq!(shape(src, "Vec<W>"), Wid::Vector(Box::new(Wid::Undecided)));
        // A nested `use` rename binds a name too.
        let renamed = "type S = i64; mod inner { use core::primitive::i32 as S; }";
        assert_eq!(shape(renamed, "S"), Wid::Undecided);
        // Once ANY inline module exists, a FILE-DECLARED name is undecided even
        // when nothing rebinds it: the function may be inside that module,
        // where the file's items are not in scope. This was the measured false
        // `Verified` (`type u32 = u64; mod inner { fn f() { let v: Vec<u32> =
        // vec![3000000000]; … } }`); its cost is that `Byte` below, which used
        // to carry, now fails closed.
        let mixed = "type Byte = u8; type W = i64; mod inner { pub type W = i32; }";
        assert_eq!(shape(mixed, "Byte"), Wid::Undecided);
        // A primitive the file does not declare is unaffected in both scopes.
        assert_eq!(shape(mixed, "u8"), Wid::Scalar("u8"));
        // And a primitive a nested module shadows is no longer the primitive.
        let shadowed = "mod inner { #[allow(non_camel_case_types)] pub struct u8; }";
        assert_eq!(shape(shadowed, "u8"), Wid::Undecided);
    }

    #[test]
    fn a_glob_bearing_file_declines_the_carry_without_refusing() {
        let src = "use vstd::prelude::*;";
        // A glob cannot be enumerated, so the whole lane is off.
        assert!(!names_of(src).enumerable);
        assert_eq!(shape(src, "u8"), Wid::Opaque(Some("u8")));
        assert!(!shape(src, "Vec<u8>").holds_width());
        assert!(render(src, "Vec<u8>", "vec![200]")
            .unwrap()
            .rendered
            .is_none());
        // ... but the BARE SCALAR recorders are unchanged, so nothing regresses.
        let ty: Type = syn::parse_str("u8").expect("type");
        assert_eq!(scalar_int_suffix(&ty, Some(&names_of(src))), Some("u8"));
        // Width-FREE leaves are unaffected; they carry nothing either way.
        assert_eq!(shape(src, "f32"), Wid::Neutral);
        // The UNQUALIFIED `core::primitive::u8` is NOT glob-proof: a glob can
        // bind `core` itself (measured with rustc — in such a file
        // `size_of::<core::primitive::u8>()` is 8 and
        // `size_of::<::core::primitive::u8>()` is 1). HEAD's recorders never
        // read a multi-segment path, so it carries no suffix either.
        assert_eq!(shape(src, "core::primitive::u8"), Wid::Opaque(None));
        assert!(render(src, "Vec<core::primitive::u8>", "vec![200]")
            .unwrap()
            .rendered
            .is_none());
        // The LEADING-`::` spelling is NOT an escape hatch any more. It is
        // capture-proof against a glob and a `mod core` (both measured), but an
        // `extern crate m as core;` at the crate root beats it (measured:
        // `lead_bytes=4`), and an unenumerable file cannot rule that out — nor
        // can it show that the `vec!` / `Vec` spine is the `std` one.
        assert_eq!(shape(src, "::core::primitive::u8"), Wid::Opaque(None));
        assert!(render(src, "Vec<::core::primitive::u8>", "vec![200]")
            .unwrap()
            .rendered
            .is_none());
        // With no glob the same file carries as before.
        assert_eq!(shape("", "u8"), Wid::Scalar("u8"));
        assert_eq!(shape("", "i32"), Wid::DefaultInt);
    }

    #[test]
    fn a_body_scope_use_poisons_the_name_it_binds() {
        // A `use` written as a STATEMENT inside a function body is invisible to
        // a table built from FILE items, and it really does rebind the name.
        let src = "type W = u64; fn f() { use other::W; let _x: W = 1; }";
        assert_eq!(shape(src, "W"), Wid::Undecided);
        assert_eq!(shape(src, "Vec<W>"), Wid::Vector(Box::new(Wid::Undecided)));
        // Including when it spells a primitive, and at any block depth.
        let prim = "fn f() { use other::u64; }";
        assert_eq!(shape(prim, "u64"), Wid::Undecided);
        let deep = "fn f() { { { use core::primitive::u32 as W; } } }";
        assert_eq!(shape(deep, "W"), Wid::Undecided);
        // ... in an inherent impl and a defaulted trait method too.
        let in_impl = "struct S; impl S { fn f() { use other::B; } }";
        assert_eq!(shape(in_impl, "B"), Wid::Undecided);
        let in_trait = "trait T { fn f() { use other::C; } }";
        assert_eq!(shape(in_trait, "C"), Wid::Undecided);
        // A body GLOB disarms the whole file exactly as a file-scope one does.
        let body_glob = "fn f() { use vstd::prelude::*; }";
        assert_eq!(shape(body_glob, "u8"), Wid::Opaque(Some("u8")));
        // SCOPED to the bound name: an unrelated body import changes nothing.
        let unrelated = "fn f() { use core::mem::size_of; }";
        assert_eq!(shape(unrelated, "u8"), Wid::Scalar("u8"));
    }

    #[test]
    fn the_core_primitive_prefix_is_an_ordinary_capturable_name() {
        // A crate-root `mod core` or a `use m as core;` redirects the whole
        // path; both were measured as false `Verified`s.
        let modded = "mod core { pub mod primitive { pub type u64 = u32; } }";
        assert_eq!(shape(modded, "core::primitive::u64"), Wid::Undecided);
        let renamed = "mod m { pub mod primitive {} } use m as core;";
        assert_eq!(shape(renamed, "core::primitive::u64"), Wid::Undecided);
        let body = "fn f() { use m as core; }";
        assert_eq!(shape(body, "core::primitive::u64"), Wid::Undecided);
        // The LEADING-`::` form is not captured by a `mod core` or a
        // `use m as core;` (both measured with rustc: eight bytes), and those
        // files are still ENUMERABLE, so it still carries. What DOES capture it
        // is `extern crate m as core;`, and that makes a file unenumerable.
        assert_eq!(shape(modded, "::core::primitive::u64"), Wid::Scalar("u64"));
        assert_eq!(shape(renamed, "::core::primitive::u64"), Wid::Scalar("u64"));
        assert_eq!(
            shape("extern crate self as core;", "::core::primitive::u64"),
            Wid::Opaque(None)
        );
        // The same guard applies to a qualified `std::vec::Vec`.
        let std_shadow = "mod std { pub mod vec { pub struct Vec; } }";
        assert_eq!(shape(std_shadow, "std::vec::Vec<u8>"), Wid::Undecided);
        assert_eq!(
            shape(std_shadow, "::std::vec::Vec<u8>"),
            Wid::Vector(Box::new(Wid::Scalar("u8")))
        );
    }

    #[test]
    fn constant_integer_arithmetic_is_decided_by_the_annotation() {
        // Every leaf is an integer literal, so rustc's inference has one
        // choice and the position's type propagates to all of them.
        let outcome = render("", "Option<u8>", "Some(200 + 50)").unwrap();
        assert_eq!(outcome.rendered.as_deref(), Some("Some(200u8 + 50u8)"));
        assert!(outcome.all_decided);
        assert_eq!(
            render("", "Vec<i8>", "vec![-100 + 50]")
                .unwrap()
                .rendered
                .as_deref(),
            Some("vec![-100i8 + 50i8]")
        );
        assert_eq!(
            render("", "(u8, u8)", "(100 + 50, 1)")
                .unwrap()
                .rendered
                .as_deref(),
            Some("(100u8 + 50u8, 1u8)")
        );
        // A SHIFT's right operand is typed independently of the result.
        assert_eq!(
            render("", "Option<u8>", "Some(1 << 3)")
                .unwrap()
                .rendered
                .as_deref(),
            Some("Some(1u8 << 3)")
        );
        // A NON-constant operand stays walled: this file cannot show the `+`
        // is the primitive impl, and the measured HEAD behaviour there is a
        // false `Verified` (`let z = 200; vec![z + 50]`).
        let walled = render("", "Vec<u8>", "vec![z + 50]").unwrap_err();
        assert!(walled.to_string().contains(ERR_WALL));
        // Each literal is still range-checked on its own.
        let out_of_range = render("", "Option<u8>", "Some(300 + 1)").unwrap_err();
        assert!(out_of_range.to_string().contains(ERR_RANGE));
    }

    #[test]
    fn floats_render_unchanged_and_are_never_counted_decided() {
        let outcome = render("", "Vec<f32>", "vec![16777216.0]").unwrap();
        // Nothing is carried, so HEAD's text stands.
        assert_eq!(outcome.rendered, None);
        assert!(outcome.complete);
        assert!(!outcome.all_decided);
        let suffixed = render("", "Vec<f32>", "vec![16777216.0f32]").unwrap();
        assert!(suffixed.all_decided);
        assert!(suffixed.complete);
    }
}
