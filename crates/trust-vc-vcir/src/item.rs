//! Items: the crate, its functions and its data types.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeMap;

mod functions;

use crate::expr::Expr;
use crate::ids::{AdtId, FnId, LocalId, SpanId};
use crate::stmt::{Block, ClauseAttrs};
use crate::ty::Ty;

/// Verus's three modes, for functions and for locals.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    /// Pure mathematical code; never runs.
    Spec,
    /// Proof code; checked, never runs.
    Proof,
    /// Executable code.
    Exec,
}

impl Mode {
    /// The name Verus prints in messages.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Spec => "spec",
            Self::Proof => "proof",
            Self::Exec => "exec",
        }
    }
}

/// What introduced a local.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocalKind {
    /// A parameter; listed in [`FnDecl::params`].
    Param,
    /// The return value; [`FnDecl::ret`].
    Return,
    /// A `let` in a body.
    Let,
    /// A temporary introduced by the producer when flattening an expression.
    Temp,
    /// A name bound inside a spec expression ([`crate::ExprKind::Let`]).
    Bound,
}

/// Prophecy classification requested at a local declaration. Parameters and
/// quantifier binders always start non-prophetic; dependencies on their actual
/// inputs are propagated at calls and through the enclosing expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum DeclProphecy {
    /// Infer once from the initializer and enclosing prophetic condition.
    #[default]
    Default,
    /// Explicitly prophetic, even when initialized with a constant.
    Prophetic,
    /// Without an initializer, infer once at the first whole-local assignment.
    /// Generated Spec [`LocalKind::Temp`] expression results additionally join
    /// independently checked branch initializations and their guard's effect.
    DelayedInfer,
}

/// A local variable of a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalDecl {
    /// Source name, used in messages and counterexamples.
    pub name: String,
    /// Its type.
    pub ty: Ty,
    /// Its mode.
    pub mode: Mode,
    /// Source prophecy marker; inference never changes this declaration.
    pub prophecy: DeclProphecy,
    /// Declared `mut`.
    pub mutable: bool,
    /// What introduced it.
    pub kind: LocalKind,
    /// Where it was declared.
    pub span: SpanId,
}

/// One `requires`, `ensures` or `recommends` clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    /// The condition.
    pub expr: Expr,
    /// Source position of the clause.
    pub span: SpanId,
    /// Proof notes and custom errors on the clause.
    pub attrs: ClauseAttrs,
}

/// Wall-clock and effort limit from `#[verifier::rlimit(..)]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rlimit {
    /// `rlimit(n)`.
    Finite(u64),
    /// `rlimit(infinity)`.
    Infinite,
}

/// Function attributes and resolved compiler facts that change verification.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FnAttrs {
    /// The producer requires Verus's scalar input fragment for retained
    /// `by(bit_vector)` queries. This restriction grants no proof authority;
    /// producers of richer typed IR may keep finite product inputs.
    pub bitvector_scalar_inputs: bool,
    /// `#[verifier::prophetic]`: every call result is prophecy-dependent,
    /// including calls whose checked body is a constant.
    pub prophetic: bool,
    /// A checked `#[verifier::inline]` spec body. Inlining substitutes its
    /// actual typed arguments; this flag grants no foreign body authority.
    pub inline: bool,
    /// `#[verifier::opaque]`: a spec function's definition starts hidden.
    pub opaque: bool,
    /// `#[verifier::external_body]`: the body is trusted, not verified.
    pub external_body: bool,
    /// Checked outer trigger groups for this local broadcast proof. The actual
    /// parameters and requires/ensures remain in this same declaration; hints
    /// confer no imported body or independent axiom authority.
    pub broadcast_triggers: Option<Vec<Vec<Expr>>>,
    /// `#[verifier::rlimit(..)]`.
    pub rlimit: Option<Rlimit>,
    /// `#[verifier::exec_allows_no_decreases_clause]` or
    /// `#[verifier::assume_termination]` on an exec function: without a
    /// `decreases` clause, its recursive calls are not checked to terminate.
    pub exec_allows_no_decreases: bool,
    /// `#[verifier::decreases_by]`: a proof function that only serves as
    /// the termination proof of a spec function ([`FnDecl::decreases_by`]).
    pub is_decreases_by: bool,
    /// The original function is a trait method implementation. This is a
    /// compiler fact, never a source attribute; generic instances retain it.
    /// Verus supplies public result typing through the trait declaration,
    /// but emits no separate recursive-helper return-type axiom here.
    pub is_trait_method_impl: bool,
    /// Native declaration and actual type arguments of a generic instance.
    /// This is producer metadata, never inferred from an instance's name.
    /// Sharing a logical definition additionally requires checked body and
    /// clause substitution; this record alone supplies no equation.
    pub instance: Option<GenericInstance>,
}

/// The declaration-level origin of a concrete generic instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericInstance {
    /// The original generic function in this crate.
    pub declaration: FnId,
    /// Complete type arguments, in the declaration's binder order.
    pub type_args: Vec<Ty>,
}

impl FnAttrs {
    pub(crate) fn without_instance(&self) -> Self {
        Self {
            bitvector_scalar_inputs: self.bitvector_scalar_inputs,
            prophetic: self.prophetic,
            inline: self.inline,
            opaque: self.opaque,
            external_body: self.external_body,
            broadcast_triggers: self.broadcast_triggers.clone(),
            rlimit: self.rlimit,
            exec_allows_no_decreases: self.exec_allows_no_decreases,
            is_decreases_by: self.is_decreases_by,
            is_trait_method_impl: self.is_trait_method_impl,
            instance: None,
        }
    }
}

/// The body of a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Body {
    /// No body: an uninterpreted spec function, a trait method declaration,
    /// an imported declaration, or the instance of a function whose calls
    /// do not matter.
    None,
    /// The defining expression of a spec function.
    Spec(Expr),
    /// The statements of an exec or proof function.
    Stmts(Block),
    /// A dual constant's executable initializer. The same expression supplies
    /// its mathematical value, conditional on all initializer checks and the
    /// declared result type. It is never an unchecked spec body.
    Constant(Expr),
}

/// What a function stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum FnRole {
    /// A function, or a method of an impl. A method implementing a trait
    /// method carries the trait's `requires` and `ensures` for its own
    /// `Self` in its clauses.
    #[default]
    Item,
    /// A trait method declaration. Its `Self` is type parameter 0, and a
    /// call through the trait at a type parameter is a call of it. Without
    /// a body there is nothing to check; a default body is checked once,
    /// for every `Self`.
    TraitDecl,
    /// A generic function at concrete type arguments, for its callers: its
    /// signature and clauses, the body of a spec function, and the body of
    /// an exec or proof function only so that the calls it makes are known.
    /// The generic function is what is checked; an instance never is.
    Instance,
    /// A foreign specification declaration, with a typed signature and no
    /// body or contract axioms. This classifies the IR; it does not establish
    /// source authority. A native producer needs its separate sealed library
    /// capability before registering such a declaration.
    Imported,
}

/// The semantics of a constant declaration, independently of its Rust proxy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstMode {
    /// A mathematical constant, checked and read in spec mode.
    Spec,
    /// An executable initializer with a shared mathematical value view.
    Dual,
    /// Each occurrence executes a fresh initializer and uses its contract.
    Exec,
}

/// The kind of declaration represented by a function-shaped verification item.
/// This is independent of whether the declaration is a generic instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum FnKind {
    /// An ordinary function or method.
    #[default]
    Function,
    /// A Rust const function; call semantics still follow its declared mode.
    ConstFunction,
    /// A constant, whose initializer and reads follow its constant mode.
    Constant(ConstMode),
    /// Stable global storage. A zero-argument statement Call reads the same
    /// typed value each time; its initializer is checked separately and never
    /// supplies a body equation. It is not an owned ordinary-call result.
    Static,
}

/// A function's checked promise about unwinding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnwindSpec {
    /// The function never unwinds.
    NoUnwind,
    /// The function never unwinds when this pure entry-state condition holds.
    NoUnwindWhen(Expr),
    /// The function may unwind.
    MayUnwind,
}

impl UnwindSpec {
    /// The conditional promise's expression, borrowed without substitution.
    #[must_use]
    pub fn condition(&self) -> Option<&Expr> {
        match self {
            Self::NoUnwindWhen(condition) => Some(condition),
            Self::NoUnwind | Self::MayUnwind => None,
        }
    }
}

/// A function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnDecl {
    /// Identity.
    pub id: FnId,
    /// Display path, used in messages only. Producers reading Verus code
    /// use Verus's spelling (`test_crate::f`), which Verus's own messages
    /// quote.
    pub name: String,
    /// Source position of the signature.
    pub span: SpanId,
    /// Spec, proof or exec.
    pub mode: Mode,
    /// What the function stands for.
    pub role: FnRole,
    /// Function, const function, constant or stable storage.
    pub kind: FnKind,
    /// Names of the type parameters, which [`crate::Ty::Param`] indexes.
    pub type_params: Vec<String>,
    /// Copy obligations assumed by this function's typing context. Every
    /// ordinary/spec call and concrete instance must discharge their actual
    /// substitution. A native producer separately authenticates these bounds.
    /// They grant no value, pointee ownership or resolution fact.
    pub copy_premises: Vec<Ty>,
    /// Every local of the function, indexed by [`LocalId`].
    pub locals: Vec<LocalDecl>,
    /// The parameters in order; each has kind [`LocalKind::Param`].
    pub params: Vec<LocalId>,
    /// The return value; kind [`LocalKind::Return`], type `()` when the
    /// function returns nothing. Postconditions refer to it.
    pub ret: LocalId,
    /// Preconditions.
    pub requires: Vec<Clause>,
    /// Postconditions; they may read [`FnDecl::ret`] and `Old` parameters.
    pub ensures: Vec<Clause>,
    /// Recommendations (checked as warnings by Verus, not verified).
    pub recommends: Vec<Clause>,
    /// An explicit unwind contract. Absent defaults to MayUnwind for Exec,
    /// and NoUnwind for Spec/Proof; this is a promise checked in the body.
    pub unwind: Option<UnwindSpec>,
    /// The `decreases` measure, lexicographic; empty when there is none.
    /// Each component is an integer spec expression over the parameters,
    /// read at entry. It matters for a function of a [`RecGroup`].
    pub decreases: Vec<Expr>,
    /// A spec function's `decreases .. when cond`: its definition holds only
    /// for arguments where `cond` holds, and its termination is checked
    /// assuming `cond`.
    pub decreases_when: Option<Expr>,
    /// A spec function's `decreases .. via f`: the proof function whose
    /// body is walked before the function's termination is checked.
    pub decreases_by: Option<FnId>,
    /// Attributes.
    pub attrs: FnAttrs,
    /// The body.
    pub body: Body,
}

/// One field of a struct or variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldDecl {
    /// Source name (a number for tuple structs).
    pub name: String,
    /// Its type.
    pub ty: Ty,
    /// Declared storage mode. Spec fields are logical snapshots, not owned
    /// executable or tracked components of the containing value.
    pub mode: Mode,
}

/// One variant of an enum; a struct has exactly one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantDecl {
    /// Source name (the struct's name for a struct).
    pub name: String,
    /// Fields in declaration order.
    pub fields: Vec<FieldDecl>,
}

/// Representation visible to the verification consumer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdtKind {
    /// A struct: exactly one variant.
    Struct,
    /// An enum.
    Enum,
    /// A Sized abstract nominal carrier. It has no variants, fields, constructors
    /// or layout in this crate. Its identity includes its complete type args.
    /// Producers must establish Sized and retain native type-acceptance
    /// policies; absence of exposed fields supplies neither fact.
    Opaque,
}

/// A struct or enum. Its fields' types may mention its type parameters
/// ([`crate::Ty::Param`]); a use of the type gives them their arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtDecl {
    /// Identity.
    pub id: AdtId,
    /// Display path.
    pub name: String,
    /// Names of the type parameters.
    pub type_params: Vec<String>,
    /// Source position.
    pub span: SpanId,
    /// Struct or enum.
    pub kind: AdtKind,
    /// Variants; one for a struct, none for an opaque nominal carrier.
    pub variants: Vec<VariantDecl>,
}

/// Why a function does not see the definition of a spec function.
///
/// Verus emits a spec function's definition once it reaches the function in
/// the order it verifies the crate in (one component of the call graph at a
/// time, dependencies first); a function it verifies earlier sees the spec
/// function uninterpreted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefOrder {
    /// Verus verifies the function before it emits the definition. The
    /// spec function stays uninterpreted there; `reveal` does not change
    /// that.
    Later,
    /// The producer cannot tell which comes first. The spec function is
    /// uninterpreted there too, and a check that is not proved while the
    /// spec function occurs in it is not a verdict.
    Unknown,
}

/// Functions that call each other: a strongly connected component of the
/// crate's call graph that holds a cycle, as Verus's call graph has it.
///
/// Every call from a member to a member of its group is a recursive call
/// (Verus's `is_recursive_call`). At each one the callee's measure, read at
/// the arguments, must be below the caller's measure at entry
/// lexicographically (Verus's `check_decrease`), unless the caller is an
/// exec function without a measure that
/// [`FnAttrs::exec_allows_no_decreases`]. A recursive spec function's
/// definition is a fixpoint, which queries unfold with fuel: a call from
/// outside the group unfolds as many times as the member's cycle length,
/// plus `n - 1` after `reveal_with_fuel(f, n)`.
///
/// The VC generator refuses every cycle of calls that no group covers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecGroup {
    /// Each member, with the length of the shortest cycle of calls from it
    /// back to itself (Verus's default fuel for it), at least 1.
    pub members: Vec<(FnId, u32)>,
}

impl RecGroup {
    /// Is `id` a member?
    #[must_use]
    pub fn contains(&self, id: FnId) -> bool {
        self.members.iter().any(|(member, _)| *member == id)
    }
}

/// A declared associated-type constructor. Names are diagnostic only: uses
/// carry the member identity and the complete ordered trait arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionDecl {
    /// Actual associated-type declaration identity.
    pub id: crate::ProjectionId,
    /// Identity of the declaring trait, distinct from the member identity.
    pub trait_id: crate::DefHash,
    /// Number of type arguments, including `Self` first.
    pub arity: usize,
    /// Display name only.
    pub name: String,
    /// Source position supplied by the producer.
    pub span: SpanId,
}

/// One member definition in a represented, closed associated implementation.
/// This is program semantics, never a saved compiler selection/owner token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionValue {
    /// The actual associated declaration, distinct from its implementation.
    pub declaration: crate::ProjectionId,
    /// Identity of the implementing associated item.
    pub definition: crate::DefHash,
    /// Its canonical closed represented type.
    pub ty: Ty,
}

/// A closed implementation whose associated members have represented values.
/// A native producer must authenticate the actual selected implementation,
/// declaration/member correspondence and compiler normalization separately.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionImpl {
    /// Identity of the implementation, not of a function or type parameter.
    pub id: crate::DefHash,
    /// Identity of the parent trait shared by every member definition.
    pub trait_id: crate::DefHash,
    /// Complete ordered, canonical ground trait arguments, Self first.
    pub arguments: Vec<Ty>,
    /// Actual associated members, never a naked arbitrary equality row.
    pub values: Vec<ProjectionValue>,
    /// Source position supplied by the producer.
    pub span: SpanId,
}

/// Everything trust-vc verifies in one crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VcCrate {
    /// Crate name, used in messages only.
    pub name: String,
    /// Physical pointer ABI observed by the producer. Verification uses
    /// [`Self::architecture`], so this is never a host-width proof shortcut.
    pub pointer_width: u32,
    /// Verification architecture, independently of the producer's host ABI.
    /// Native Verus defaults to both 32/64; a fixed-width IR producer may
    /// explicitly bind one architecture.
    pub architecture: crate::bitvector::Architecture,
    /// Data types.
    pub adts: Vec<AdtDecl>,
    /// Associated-type constructors. These declare type identities only;
    /// they do not assert projection equalities or provide value layouts.
    pub projections: Vec<ProjectionDecl>,
    /// Represented closed associated implementations. These reduce the type
    /// language; they emit no solver equality axiom or native capability.
    pub projection_impls: Vec<ProjectionImpl>,
    /// Functions.
    pub fns: Vec<FnDecl>,
    /// For a function with a body to check (an exec or proof function, or a
    /// recursive spec function, whose termination is checked), the spec
    /// functions whose definitions it may not see ([`DefOrder`]). Every
    /// other definition is visible to it (unless opaque).
    pub def_order: BTreeMap<FnId, BTreeMap<FnId, DefOrder>>,
    /// The groups of recursive functions; a function is in one group at
    /// most.
    pub rec_groups: Vec<RecGroup>,
}

impl AdtDecl {
    /// The type of field `field` of variant `variant` at the type arguments
    /// `args`.
    #[must_use]
    pub fn field_ty(&self, variant: u32, field: u32, args: &[Ty]) -> Option<Ty> {
        if self.kind == AdtKind::Opaque {
            return None;
        }
        self.variants
            .get(variant as usize)?
            .fields
            .get(field as usize)
            .map(|f| f.ty.subst(args))
    }
}

impl VcCrate {
    /// An empty crate for a 64-bit target.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            pointer_width: 64,
            architecture: crate::bitvector::Architecture::Exactly(64),
            adts: Vec::new(),
            projections: Vec::new(),
            projection_impls: Vec::new(),
            fns: Vec::new(),
            def_order: BTreeMap::new(),
            rec_groups: Vec::new(),
        }
    }

    /// The function with identity `id`.
    #[must_use]
    pub fn fn_decl(&self, id: FnId) -> Option<&FnDecl> {
        self.fns.iter().find(|decl| decl.id == id)
    }

    /// The group of recursive functions `id` belongs to, if any.
    #[must_use]
    pub fn rec_group(&self, id: FnId) -> Option<&RecGroup> {
        self.rec_groups.iter().find(|group| group.contains(id))
    }

    /// The data type with identity `id`.
    #[must_use]
    pub fn adt(&self, id: AdtId) -> Option<&AdtDecl> {
        self.adts.iter().find(|decl| decl.id == id)
    }
}
