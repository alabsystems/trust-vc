//! Statements: the bodies of exec and proof functions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A body is structured control flow over places. Every effect is a
//! statement: calls, assignments, assertions, reveals. Expressions inside
//! statements are pure (see [`crate::expr`]).

use crate::expr::{Expr, Place};
use crate::ids::{FnId, LocalId, LoopId, SiteId, SpanId};
use crate::ty::Ty;

/// Verus attributes attached to a clause, an assertion or an assumption.
///
/// Both lists keep every occurrence the source had, so the checker can report
/// a duplicate the way Verus does.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct ClauseAttrs {
    /// `#[verifier::proof_note("..")]`: extra text for the failure message.
    pub proof_notes: Vec<String>,
    /// `#[verifier::custom_err("..")]`: replaces the failure message.
    pub custom_errs: Vec<String>,
}

impl ClauseAttrs {
    /// Does the clause carry a proof note or a custom error? Verus encodes
    /// such an `ensures` clause as a labelled axiom, `label => clause`, whose
    /// label is a free boolean (`vir/src/sst_to_air_func.rs`,
    /// `req_ens_to_air`; `air/src/smt_verify.rs`, `label_asserts`), so a
    /// caller can never assume it.
    #[must_use]
    pub fn is_labelled(&self) -> bool {
        !self.proof_notes.is_empty() || !self.custom_errs.is_empty()
    }
}

/// A sequence of statements.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Block {
    /// The statements, executed in order.
    pub stmts: Vec<Stmt>,
}

impl Block {
    /// A block of the given statements.
    #[must_use]
    pub const fn new(stmts: Vec<Stmt>) -> Self {
        Self { stmts }
    }
}

/// Where a loop invariant must hold (Verus's `LoopInvariantKind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvariantKind {
    /// `invariant_except_break`: on entry and at the start of every
    /// iteration, but not where the loop is left by `break`.
    ExceptBreak,
    /// `invariant`: on entry, at the start of every iteration and at every
    /// exit.
    Always,
    /// A loop `ensures`: at every exit.
    Ensures,
}

/// One clause of a loop's specification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopInvariant {
    /// Where it must hold.
    pub kind: InvariantKind,
    /// The condition, a spec expression.
    pub expr: Expr,
    /// Source position of the clause.
    pub span: SpanId,
}

/// The condition of a `while` loop: the statements that compute it, run
/// before every iteration, and its value after them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopCond {
    /// Effects of the condition, in order.
    pub block: Block,
    /// The condition's value, a `bool` exec expression.
    pub expr: Expr,
}

/// The check sites of a loop itself; `break` and `continue` have their own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopSites {
    /// The invariants on entry.
    pub entry: SiteId,
    /// The invariants and the decreases at the end of the body.
    pub end: SiteId,
    /// The exit of a `while` whose condition is false, where Verus checks
    /// the exit invariants as at a `break`.
    pub exit: SiteId,
}

/// `while cond { body }` or `loop { body }` with Verus's loop
/// specification.
///
/// The semantics are Verus's (`vir/src/ast_to_sst.rs` and
/// `sst_to_air.rs`, `StmX::Loop`): the invariants that hold on entry are
/// checked before the loop; every local the loop assigns has an arbitrary
/// value of its type at the start of an iteration, where those invariants
/// are assumed; they are checked again at the end of the body and at every
/// `continue`, and the exit invariants at every `break`. With `isolation`
/// the body is checked knowing only the invariants and the types of the
/// locals, not what held before the loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loop {
    /// Identity within the function.
    pub id: LoopId,
    /// Verus's `loop_isolation`.
    pub isolation: bool,
    /// `#[verifier::allow_complex_invariants]`; only without isolation.
    pub allow_complex_invariants: bool,
    /// The condition of a `while`; `None` for `loop`.
    pub cond: Option<LoopCond>,
    /// `invariant_except_break`, `invariant` and `ensures` clauses, in
    /// that order.
    pub invariants: Vec<LoopInvariant>,
    /// The `decreases` measure, lexicographic; empty when there is none.
    pub decreases: Vec<Expr>,
    /// The body.
    pub body: Block,
    /// Check sites.
    pub sites: LoopSites,
}

/// A statement with its source position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stmt {
    /// Source position.
    pub span: SpanId,
    /// The statement itself.
    pub kind: StmtKind,
}

impl Stmt {
    /// A statement from its parts.
    #[must_use]
    pub const fn new(span: SpanId, kind: StmtKind) -> Self {
        Self { span, kind }
    }
}

/// Statement forms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtKind {
    /// Declare a local (kind `Let` or `Temp`), optionally initialised. An
    /// uninitialised local has an arbitrary represented value until assigned,
    /// except that abstract Poly storage supplies no value or type membership
    /// before initialization.
    Let {
        /// The local declared.
        local: LocalId,
        /// Its initial value.
        init: Option<Expr>,
    },
    /// Write a value to a place.
    Assign {
        /// The place written.
        place: Place,
        /// The value.
        value: Expr,
    },
    /// Borrow one initialized storage place as a new opaque mutable reference.
    /// The generator relates its current projection to the old storage value
    /// and writes its future projection back to that same typed place.
    BorrowMut {
        /// An already declared, uninitialized local of type `MutRef(place_ty)`.
        dest: LocalId,
        /// The storage borrowed, including any typed parent projections.
        place: Place,
    },
    /// Call an exec or proof function. `site` is where the callee's
    /// preconditions are checked.
    Call {
        /// The callee.
        callee: FnId,
        /// One type per type parameter of the callee; its parameter and
        /// result types are read with them.
        type_args: Vec<Ty>,
        /// Arguments, one per parameter.
        args: Vec<Expr>,
        /// Where the result goes; `None` discards it.
        dest: Option<Place>,
        /// Precondition site.
        site: SiteId,
    },
    /// `assert(expr)`: checked at `site`, then assumed.
    Assert {
        /// The asserted condition.
        expr: Expr,
        /// The check site.
        site: SiteId,
        /// Proof notes and custom errors.
        attrs: ClauseAttrs,
    },
    /// `assert_bitvector_by`: an isolated question using only its explicit
    /// requirements. The surrounding path checks each requirement and learns
    /// each ensures afterward; its ambient facts never enter the BV solver.
    AssertBitVector {
        /// Requirements, checked with the ordinary scalar encoding first.
        requires: Vec<crate::item::Clause>,
        /// At least one Boolean conclusion, each checked in isolation.
        ensures: Vec<crate::item::Clause>,
        /// Actual architecture cases of the isolated encoding.
        architecture: crate::bitvector::Architecture,
        /// The assertion site, shared by its clause checks.
        site: SiteId,
    },
    /// `assume(expr)`.
    Assume {
        /// The assumed condition.
        expr: Expr,
        /// Proof notes and custom errors (reported under `--no-cheating`).
        attrs: ClauseAttrs,
    },
    /// `if cond { then_block } else { else_block }`.
    If {
        /// The condition.
        cond: Expr,
        /// Taken when the condition holds.
        then_block: Block,
        /// Taken otherwise.
        else_block: Block,
    },
    /// Leave the function. `site` is where the postconditions are checked.
    /// `value` is `None` exactly when the function returns `()`.
    Return {
        /// The returned value.
        value: Option<Expr>,
        /// Postcondition site.
        site: SiteId,
    },
    /// `reveal(f)` / `reveal_with_fuel(f, n)`: make a spec function's
    /// definition visible from here on.
    Reveal {
        /// The spec function.
        callee: FnId,
        /// Fuel for recursive functions; `None` means the default.
        fuel: Option<u32>,
    },
    /// Enable the actual local broadcast proof's universal contract from this
    /// source location. Its declaration supplies every binder and clause.
    BroadcastUse {
        /// Exact declaration identity, never a source-name lookup.
        callee: FnId,
    },
    /// `hide(f)`: stop using a spec function's definition from here on.
    Hide {
        /// The spec function.
        callee: FnId,
    },
    /// A ghost block (`proof { .. }` in exec code): proof-mode statements
    /// that do not run.
    Ghost(Block),
    /// A proof block in executable code whose original Unit-valued tail is
    /// retained for raw value-mode and prophecy checks before Unit erasure.
    /// There is no producer-supplied mode override.
    GhostTail {
        /// Proof statements preceding the actual tail expression.
        block: Block,
        /// The original tail, including any generated result temporary.
        tail: Expr,
    },
    /// A nested block.
    Block(Block),
    /// A loop; exec code only. The statement's span is the loop's header.
    Loop(Box<Loop>),
    /// Leave the enclosing loop `target`. `site` is where its exit
    /// invariants are checked.
    Break {
        /// The loop left.
        target: LoopId,
        /// Invariant site.
        site: SiteId,
    },
    /// Start the next iteration of the enclosing loop `target`. `site` is
    /// where its invariants and decreases are checked.
    Continue {
        /// The loop restarted.
        target: LoopId,
        /// Invariant and decreases site.
        site: SiteId,
    },
    /// The end of an expression of type `!` that rustc coerces to another
    /// type (Verus's `NeverToAny`). No path reaches it. As in Verus
    /// (`ast_to_sst.rs`), the statements after it in its block are not
    /// verified and their assignments do not count; they are still read,
    /// so what Verus rejects anywhere is rejected there too.
    ///
    /// A block ends the same way after a `return`, after an `if` both of
    /// whose branches end, and after a `loop` without a `break`, but not
    /// after a plain `break;` or `continue;` statement: Verus keeps the
    /// statements that follow those.
    Unreachable,
}
