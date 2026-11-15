// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An ACYCLIC trust-ir function body as a path-condition relation.
//!
//! This is the compiler-lane replacement for the syn front end's body
//! extraction, redone over trust-ir rather than ported. It turns a function into
//! variable declarations plus assumptions that RELATE those variables, which is
//! the shape `VerificationContext` verifies over.
//!
//! # The encoding
//!
//! Each reachable block `b` gets a boolean **path-condition variable** `pc$b`
//! with an EXACT defining equation:
//!
//! ```text
//! pc$entry == true
//! pc$s     == OR over incoming edges p->s of (pc$p && guard(p->s))
//! ```
//!
//! and every fact the block establishes is asserted only under its own path
//! condition:
//!
//! ```text
//! assume(pc$b => v == <the instruction's value>)     // SSA definitions
//! assume(pc$p && guard => param == arg)              // block params (phi)
//! assume(pc$r => _0 == <returned value>)             // returns
//! ```
//!
//! Two properties make this sound rather than merely convenient.
//!
//! * Every assumption is TRUE in the program: a conditional definition is
//!   weaker than an unconditional one, and weakening an assumption can only
//!   make a proof fail, never succeed.
//! * The path conditions are DEFINED, not free. That matters more than it
//!   looks: if `pc$b` were merely implied (`pc$p && g => pc$s`) nothing would
//!   force it false on the branch not taken, two sibling blocks could both be
//!   "live", and `_0` would be pinned to two different values at once — an
//!   inconsistent assumption set, which proves everything. With exact
//!   equations, mutual exclusion follows inductively from `pc$entry == true`.
//!
//! No `Ite` is needed anywhere, which is why this lane does not have to widen
//! the boundary expression to carry one.
//!
//! # What it refuses
//!
//! Loops (any back edge), `Inst::Unreachable`, memory (`Alloca`/`Load`/`Store`
//! and every pointer/aggregate/atomic/borrow instruction), `Inst::Assert`,
//! indirect calls, calls into a recursion cycle, calls to a callee carrying a
//! precondition, and every type outside the scalar fragment. Each declines BY
//! NAME.
//!
//! Several more are about the ENCODING rather than the fragment, and each was a
//! false `Discharged` before it was a decline:
//!
//! * **Reserved names.** `variables` is ONE flat namespace, so a producer value
//!   spelled `_0` and the return place are the same variable (and `pc$b => _0 ==
//!   …` then pins the producer's value to the returned one), and a value spelled
//!   `pc$0` IS block 0's path condition (which `pc$0 == true` forces true). Both
//!   are refused by name; renaming would silently change what a clause spelling
//!   that name resolves to. The same two gates, plus the shadowing gate, apply to
//!   a CALLEE's parameter names, because a callee contract is rebound onto the
//!   caller's variables by name.
//! * **A `CastOp` that disagrees with its operand's sort.** `TrustExpr::Cast`
//!   carries only two sorts; the encoder derives the extension from the SOURCE
//!   sort's signedness and narrow-vs-extend from the two widths. trust-ir's
//!   interpreter instead reads the raw bits in two's complement for `SExt`
//!   whatever the source type says, so a `SExt` from an unsigned source would be
//!   modelled as a ZERO extension — a claim false under the IR's own reference
//!   semantics.
//! * **A terminator that is not its block's last instruction.** Successors come
//!   from `Block::terminator()` (`body.last().filter(is_terminator)`); reading
//!   `body.last()` instead makes a trailing dead `Return` the terminator and
//!   drops the real branch, so the lane would model a different CFG than the
//!   module declares. `trust-ir-build`'s `validate_module` rejects the shape, but
//!   this crate does not depend on it and runs only
//!   `NativeVerificationBundle::validate()`.
//!
//!
//! # Path-local contradiction: the class, and the four gates that close it
//!
//! Every block fact is asserted under that block's path condition (`pc$b => v ==
//! …`). So if ONE block's facts contradict each other, that path simply has no
//! model: the solver never explores it, the counterexample that lives on it
//! disappears, and the obligation comes back proved over the paths that survive.
//! The engine's `VacuousTruth` detector does NOT see this — it fires when the
//! WHOLE assumption set is contradictory, and a contradiction confined to one
//! arm leaves the rest satisfiable. There is no counterexample and no `Unknown`;
//! the row reads `Verified` and mints a kernel-checked certificate. It is the
//! most dangerous failure this lane has, because every symptom is absent.
//!
//! Nothing here makes a path's satisfiability an obligation, so the defence is
//! structural: refuse every shape that can create the contradiction.
//!
//! * **Duplicate `Switch` case values.** The per-case guards are mutually
//!   exclusive only when the values are DISTINCT; two cases carrying one value
//!   make both arms live at once and their facts collide. trust-ir's interpreter
//!   takes the first matching case, so the program is perfectly definite — the
//!   lane refuses rather than inventing first-match guards for a shape
//!   `validate_module` rejects outright.
//! * **An integer constant outside the sort it is used at.** trust-ir's
//!   reference semantics MASK it (`InterpretInt::from_i128`), so `256` at `u8`
//!   IS `0`; emitting the literal as written yields an equality nothing
//!   satisfies — which drops the `Switch` arm the program actually takes, or
//!   kills the block that defines the value. `validate_module` types every
//!   `SwitchCase.value` against its selector (trust-ir's shared switch-literal
//!   contract), so a bundle is refused by the producer-validator input gate
//!   first; this gate keeps the lane closed for a module lowered without it.
//! * **A `ValueId` defined twice.** Two defining equations for one variable on
//!   one path, which contradict whenever they disagree.
//! * **A value used before it is defined.** The general case of the previous
//!   gate: `v == v + 1`, or a cycle of definitions, is unsatisfiable without any
//!   value being defined twice. Valid SSA always passes, because a definition
//!   dominates its uses and a dominator precedes in every topological order.
//!
//! What remains is NOT a defect but must be read as what it is: an
//! `Inst::Assume` and a callee's published `ensures` are PRODUCER claims, and a
//! false one of either kills a path the same way. Neither is trust-vc's to
//! second-guess at this pin (an `assume` is a fact the producer asserted; a
//! callee with no opacity marker must be read contract-only), so both are
//! disclosed instead: every outcome that rests on one carries a `BodyAssume` or
//! `CalleeContract` premise naming it. A consumer that reads the verdict without
//! the premise vector is reading a trusted assertion as a proof.
//!
//! Two of those deserve their reason stated, because both look like
//! conservatism and are not:
//!
//! * **`Inst::Unreachable` is never assumed away.** A block that ends in
//!   `Unreachable` is a path the producer claims cannot happen. Encoding that
//!   claim as `pc$b => false` would be `assume(false)` on that path, and every
//!   obligation is provable under it. The claim is not ours to make.
//! * **`Alloca`/`Load`/`Store` are not promoted first.** trust-ir ships
//!   `mem2reg::promote_allocas_function`, and running it would widen this lane
//!   considerably — but it REMOVES instructions, and `ObligationSite` is a
//!   `(block, inst_index)` anchor. Promoting on a clone silently renumbers the
//!   indices every obligation binds to, so an obligation could be decided
//!   against the wrong instruction. Declining keeps the anchors exact.

use super::formula::FormulaDecoder;
use super::ty::TypeDecoder;
use super::{formula, Decline, Scope, ScopeEntry, RESULT_VAR};
use crate::{
    TrustArithOp, TrustCompareOp, TrustExpr, TrustLogicOp, TrustSort, TrustVcNativeTrustIrPremise,
    TrustVcNativeTrustIrPremiseKind,
};
use std::collections::{BTreeMap, BTreeSet};
use trust_ir::inst::{BinOp, CastOp, ICmpOp, Inst, UnOp};
use trust_ir::{
    Block, Constant, DropResolution, FuncId, Function, Module, ObligationKind, ObligationSite,
    ProofObligation, ProofStatus, Ty, ValueId,
};

/// The lowered body: declarations plus the assumptions that relate them.
#[derive(Debug)]
pub(crate) struct BodyRelation {
    /// Every variable the unit must declare, by its unit-level name.
    pub(crate) variables: BTreeMap<String, TrustSort>,
    /// `(id, predicate)` assumptions, in emission order.
    pub(crate) assumptions: Vec<(String, TrustExpr)>,
    /// The scope a contract clause of THIS function resolves against.
    pub(crate) scope: Scope,
    /// Facts this relation rests on but did not prove.
    pub(crate) premises: Vec<TrustVcNativeTrustIrPremise>,
}

/// One CFG edge, with the block arguments THAT EDGE passes.
///
/// SOUNDNESS: the arguments belong to the edge, not to the target block. One
/// terminator can reach the same block twice — a `CondBr` whose two targets are
/// the same block, a `Switch` where a case and the default (or two cases) share
/// one — and those two edges may pass DIFFERENT arguments. Resolving the
/// argument list by target alone binds both edges to the first list found, so
/// the phi assumption `pc$p && guard => param == arg` asserts something FALSE in
/// the program, and under a false assumption every obligation is provable.
#[derive(Debug, Clone)]
struct Edge {
    from: u32,
    guard: TrustExpr,
    args: Vec<ValueId>,
}

/// What one callee's published rows contributed, after adjudication.
///
/// See [`Builder::callee_contract_facts`] for the invariant this type exists to
/// make explicit: nothing reaches `ensures` on the strength of a label.
struct CalleeContractFacts<'a> {
    /// The def-site `ensures` rows this lane may assume, each paired with the
    /// EVIDENCE that was actually checked for it — produced by
    /// [`Builder::established_callee_ensures`], never composed at the premise.
    /// Round 7 found the premise hard-coding "with a lineage-bound `CleanCic`
    /// certificate" independently of the check, so that under a relaxed gate it
    /// asserted evidence nothing had tested.
    ensures: Vec<(&'a ProofObligation, String)>,
    /// Rows deliberately NOT imported, each naming the rule that excluded it.
    omitted: Vec<String>,
}

/// The instruction currently being lowered, for [`RowAttribution::of`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CallPosition {
    /// The function containing the call — the CALLER.
    function: FuncId,
    block: u32,
    inst_index: u32,
}

impl CallPosition {
    /// Does `site` name THIS instruction?
    fn names(self, site: ObligationSite) -> bool {
        site.function == self.function
            && site.block.index() == self.block
            && site.inst_index == self.inst_index
    }
}

/// Whose row is this, as the PRODUCER's scoping fields answer it.
///
/// [`ProofObligation::function`] scopes a row to a function and
/// [`ObligationSite::function`] scopes its instruction site to one; upstream
/// requires them to AGREE only when both are present, so either may be the only
/// one set. Reading just one of them is a silent pre-filter over producer data,
/// which is the round-6/round-7 fail-open class. See
/// [`Builder::callee_contract_facts`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RowAttribution {
    /// The row's `site` names an instruction that CALLS this callee — this call,
    /// or another call to the same callee elsewhere in the module. ROUND 8,
    /// MAJOR 1: this is a POSITIVE rule and it OVERRIDES `function`, because a
    /// call-site VC lives in the CALLER and is scoped to it.
    ThisCallSite,
    /// `function` or `site.function` positively names this callee.
    ThisCallee,
    /// At least one of the two is set, neither names this callee, and the site
    /// (if any) does not name a call to it. This is the ONLY positive exclusion.
    AnotherFunction,
    /// Neither is set. The producer said nothing about whose row it is, so it
    /// cannot be excluded from being this callee's — it is adjudicated for
    /// REFUSAL, and never as a source of an imported fact.
    Unattributed,
    /// The row carries a `site` that does not resolve to an instruction in this
    /// module. Nothing can be concluded from an unresolvable position, so the
    /// row is adjudicated rather than excluded.
    UnresolvableSite,
}

impl RowAttribution {
    /// ROUND 8, MAJOR 1 — THE POSITIVE RULE, and why it comes first.
    ///
    /// A `Precondition` anchored AT A CALL INSTRUCTION is the DOCUMENTED shape
    /// of a call-site VC: [`ObligationSite`]'s own doc says `site` names the
    /// `(block, inst_index)` of the instruction whose check the obligation
    /// states, and that instruction lives in the CALLER. So both `function` and
    /// `site.function` name the caller, the pre-round-8 attribution called the
    /// row [`RowAttribution::AnotherFunction`], `callee_contract_facts` skipped
    /// it before adjudication, and the callee's `ensures` was imported WITH NO
    /// GUARD — never used as a guard, never recorded in the
    /// `UnimportedCalleeObligation` premise, and never discharged (E3 declines
    /// every sited row as a requested row). Nobody owed it.
    ///
    /// MEASURED (round 8, probe R8-P3, every shape producer-valid through
    /// `validate_module`): callee-scoped-no-site, callee-scoped-sited-in-callee,
    /// unscoped-sited-in-callee and wholly-unattributed all fired the guard;
    /// CALLER-scoped sited AT THE CALL and unscoped sited at the call did NOT.
    /// Probe R8-P7b showed the `ensures` imported with premises
    /// `["CalleeContract"]` and guard assumptions `[]`.
    ///
    /// It was blocked end-to-end only because the `Certified` import path is
    /// structurally dead in this build (E12), which is not a closure.
    ///
    /// THE RULE: a row whose `site` names an instruction that CALLS this callee
    /// is THIS CALLEE'S, whichever function it is scoped to. It is checked
    /// FIRST, so it overrides the `function` test rather than being overridden
    /// by it.
    ///
    /// WHY IT IS NOT LIMITED TO THIS CALL. A precondition row anchored at ANY
    /// call to this callee is evidence that the callee HAS a `requires` a caller
    /// must establish; importing its `ensures` unguarded here would rest on a
    /// guard nothing established at THIS call. Restricting the rule to the
    /// current instruction would leave a producer that emits the VC at only one
    /// of two call sites able to reopen exactly this hole one call over. The
    /// measured cost is in `callee_contract_facts`'s own "measured cost"
    /// section.
    fn of(
        obligation: &ProofObligation,
        callee_id: FuncId,
        module: &Module,
        call: CallPosition,
    ) -> Self {
        let scoped = obligation.function;
        let sited = obligation.site.map(|site| site.function);
        if let Some(site) = obligation.site {
            match call_target_at(module, site) {
                SiteTarget::CallsFunction(target) if target == callee_id => {
                    return RowAttribution::ThisCallSite;
                }
                SiteTarget::Unresolvable | SiteTarget::IndirectCall => {
                    // `call.names(site)` is checked anyway: the instruction this
                    // builder is lowering is resolvable by construction, so a
                    // site that names it can never be `Unresolvable`. Kept for
                    // the reader — the two are independent facts.
                    if call.names(site) {
                        return RowAttribution::ThisCallSite;
                    }
                    return RowAttribution::UnresolvableSite;
                }
                SiteTarget::CallsFunction(_) | SiteTarget::NotACall => {}
            }
        }
        if scoped.is_none() && sited.is_none() {
            RowAttribution::Unattributed
        } else if scoped == Some(callee_id) || sited == Some(callee_id) {
            RowAttribution::ThisCallee
        } else {
            RowAttribution::AnotherFunction
        }
    }

    /// How a decline names this row's provenance, so the message says why a row
    /// the producer never scoped is being adjudicated against this callee.
    fn phrase(self, callee_name: &str) -> String {
        match self {
            RowAttribution::ThisCallee => format!("published by callee `{callee_name}`"),
            RowAttribution::ThisCallSite => format!(
                "anchored at an instruction that CALLS `{callee_name}` — a call-site VC lives in \
                 the CALLER, so the function it is scoped to does not make it the caller's own"
            ),
            RowAttribution::Unattributed => format!(
                "attributed to NO function by the producer (neither `function` nor `site`), so \
                 it cannot be excluded from being callee `{callee_name}`'s"
            ),
            RowAttribution::UnresolvableSite => format!(
                "anchored at a position that does not resolve to a DIRECT call in this module (a \
                 missing instruction, an indirect call that names no callee, or a drop whose \
                 glue does not resolve), so it cannot be excluded from being callee \
                 `{callee_name}`'s"
            ),
            RowAttribution::AnotherFunction => {
                format!("not callee `{callee_name}`'s")
            }
        }
    }
}

/// What the instruction an [`ObligationSite`] names actually is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SiteTarget {
    /// A direct `Call` naming this function.
    CallsFunction(FuncId),
    /// Resolvable and not a call at all.
    NotACall,
    /// A call whose callee this module does not name: an indirect call of any
    /// unwind shape, or a drop whose glue does not resolve. Nothing can be
    /// concluded about which callee it binds — including that it is not this
    /// one. Adjudicated, never excluded.
    IndirectCall,
    /// The site names a function, block or instruction index this module does
    /// not have.
    Unresolvable,
}

/// Resolve the instruction an [`ObligationSite`] names.
fn call_target_at(module: &Module, site: ObligationSite) -> SiteTarget {
    let Some(function) = module.function_by_id(site.function) else {
        return SiteTarget::Unresolvable;
    };
    let Some(block) = function.blocks.iter().find(|block| block.id == site.block) else {
        return SiteTarget::Unresolvable;
    };
    let Ok(index) = usize::try_from(site.inst_index) else {
        return SiteTarget::Unresolvable;
    };
    let Some(node) = block.body.get(index) else {
        return SiteTarget::Unresolvable;
    };
    match &node.inst {
        Inst::CallIndirect { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::InvokeIndirect { .. } => SiteTarget::IndirectCall,
        other => match direct_callee(module, other) {
            Some(DirectCallee::Named(callee)) => SiteTarget::CallsFunction(callee),
            Some(DirectCallee::UnresolvedDropGlue) => SiteTarget::IndirectCall,
            None => SiteTarget::NotACall,
        },
    }
}

/// The function an instruction calls by name, when it calls one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DirectCallee {
    Named(FuncId),
    /// A drop of a type with no single glue row: it calls a function, but
    /// the module does not say which.
    UnresolvedDropGlue,
}

/// Every instruction that transfers control to a function the module names:
/// a direct call of either unwind shape and its invoke twin, a drop or
/// drop-invoke (a drop is a call of its type's glue), and a sited check (a
/// failing one calls its panic entry). Indirect calls name no function and
/// are not listed here.
fn direct_callee(module: &Module, inst: &Inst) -> Option<DirectCallee> {
    match inst {
        Inst::Call { callee, .. }
        | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => Some(DirectCallee::Named(*callee)),
        Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => {
            Some(match module.drop_glue_for(ty) {
                DropResolution::Resolved(glue) => DirectCallee::Named(glue),
                DropResolution::Unresolved | DropResolution::Ambiguous => {
                    DirectCallee::UnresolvedDropGlue
                }
            })
        }
        other => other
            .panic_site()
            .map(|site| DirectCallee::Named(site.entry)),
    }
}

struct Builder<'a> {
    module: &'a Module,
    function: &'a Function,
    function_id: FuncId,
    types: TypeDecoder,
    blocks: BTreeMap<u32, &'a Block>,
    /// Reachable blocks in a topological order (predecessors first).
    order: Vec<u32>,
    /// `target -> the edges that reach it`.
    incoming: BTreeMap<u32, Vec<Edge>>,
    /// Unit-level variable name and sort for each SSA value.
    values: BTreeMap<u32, ScopeEntry>,
    relation: BodyRelation,
    next_assumption: usize,
}

/// Build the relation for one acyclic scalar function body.
pub(crate) fn lower_body(
    module: &Module,
    function: &Function,
    function_id: FuncId,
    types: TypeDecoder,
) -> Result<BodyRelation, Decline> {
    // The weight blob table (trust-ir wire v70) holds the bytes a
    // `Constant::TensorBlob` names by digest. The lane has no tensor sort and
    // reads no blob, so a module carrying one declines whole, by the table's
    // name, before any body is lowered.
    if !module.blobs.is_empty() {
        return Err(Decline::new(format!(
            "the module carries {} weight blob row(s) (`Module.blobs`), which the discharge \
             lane does not model: it has no tensor sort",
            module.blobs.len()
        )));
    }
    let mut blocks = BTreeMap::new();
    for block in &function.blocks {
        if blocks.insert(block.id.index(), block).is_some() {
            return Err(Decline::new(format!(
                "function `{}` declares block {} twice",
                function.name,
                block.id.index()
            )));
        }
    }
    reject_misplaced_terminators(function)?;
    let order = topological_order(function, &blocks)?;

    let mut builder = Builder {
        module,
        function,
        function_id,
        types,
        blocks,
        order,
        incoming: BTreeMap::new(),
        values: BTreeMap::new(),
        relation: BodyRelation {
            variables: BTreeMap::new(),
            assumptions: Vec::new(),
            scope: Scope::new(),
            premises: Vec::new(),
        },
        next_assumption: 0,
    };
    builder.build()?;
    Ok(builder.relation)
}

// ---------------------------------------------------------------------------
// CFG shape
// ---------------------------------------------------------------------------

/// Refuse a block whose terminator is not its LAST instruction.
///
/// SOUNDNESS: a block's successors come from its terminator, and trust-ir spells
/// that `Block::terminator()` = `body.last().filter(is_terminator)`. A block
/// carrying a `CondBr` mid-body followed by a dead `Return` therefore has NO
/// terminator by that reading — but reading `body.last()` instead makes the dead
/// `Return` the terminator, the branch is silently dropped, and the lane models
/// a DIFFERENT CFG than the module declares (every successor block vanishes, and
/// the obligation is decided against the wrong return).
///
/// `trust-ir-build`'s `validate_module` rejects the shape, but this crate does
/// not depend on that crate and runs only `NativeVerificationBundle::validate()`
/// — the same hand-built/replayed-bundle threat model the edge-keyed block
/// arguments were fixed under. Checked over EVERY declared block, not only the
/// reachable ones, because reachability is computed from the very edges this
/// guards.
fn reject_misplaced_terminators(function: &Function) -> Result<(), Decline> {
    for block in &function.blocks {
        let last = block.body.len().saturating_sub(1);
        for (index, node) in block.body.iter().enumerate() {
            if node.inst.is_terminator() && index != last {
                return Err(Decline::new(format!(
                    "block {} of `{}` carries `{}` at instruction {index}, which is a TERMINATOR \
                     but not the block's last instruction: its successors would be read from the \
                     trailing instruction instead and this branch silently dropped, so the lane \
                     would model a different CFG than the module declares",
                    block.id.index(),
                    function.name,
                    inst_name(&node.inst)
                )));
            }
        }
    }
    Ok(())
}

/// Reachable blocks, predecessors first — or a decline naming the back edge.
///
/// A back edge is a LOOP, and a loop needs an invariant anchor this schema does
/// not carry (`ObligationSite` is an instruction anchor, not a loop header).
/// Unrolling it would be a bounded check reported as a proof.
fn topological_order(
    function: &Function,
    blocks: &BTreeMap<u32, &Block>,
) -> Result<Vec<u32>, Decline> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Open,
        Done,
    }
    let entry = function.entry.index();
    if !blocks.contains_key(&entry) {
        return Err(Decline::new(format!(
            "function `{}` names entry block {entry}, which it does not declare",
            function.name
        )));
    }

    let mut mark: BTreeMap<u32, Mark> = BTreeMap::new();
    let mut order = Vec::new();
    // Iterative DFS: (block, index of the next successor to visit).
    let mut stack: Vec<(u32, usize)> = vec![(entry, 0)];
    mark.insert(entry, Mark::Open);
    while let Some((block_id, cursor)) = stack.pop() {
        let block = blocks.get(&block_id).copied().ok_or_else(|| {
            Decline::new(format!(
                "function `{}` branches to block {block_id}, which it does not declare",
                function.name
            ))
        })?;
        let successors = successor_ids(block);
        if cursor < successors.len() {
            let next = successors[cursor];
            stack.push((block_id, cursor + 1));
            match mark.get(&next) {
                Some(Mark::Open) => {
                    return Err(Decline::new(format!(
                        "function `{}` has a back edge from block {block_id} to block {next}: \
                         the discharge lane is acyclic-only, and a loop needs an invariant \
                         anchor the pinned trust-ir schema does not carry",
                        function.name
                    )))
                }
                Some(Mark::Done) => {}
                None => {
                    mark.insert(next, Mark::Open);
                    stack.push((next, 0));
                }
            }
        } else {
            mark.insert(block_id, Mark::Done);
            order.push(block_id);
        }
    }
    order.reverse();
    Ok(order)
}

/// The values one instruction READS, for the instructions this lane models.
///
/// An instruction outside the fragment contributes nothing: it declines by name
/// before any of its operands reaches the relation. `Inst` is `#[non_exhaustive]`
/// upstream, so the catch-all is required — and it is the same fail-closed
/// shape, because an unrecognized instruction cannot be lowered either.
fn operand_values(inst: &Inst) -> Vec<ValueId> {
    match inst {
        Inst::Copy { operand, .. }
        | Inst::UnOp { operand, .. }
        | Inst::Cast { operand, .. }
        | Inst::Assume { cond: operand } => vec![*operand],
        // The kind's operands and a run-time location are read only when the
        // check fails; an `Assert` declines by name below either way.
        Inst::Assert { cond, kind, site } => {
            let mut used = vec![*cond];
            used.extend(kind.operands().into_iter().flatten());
            used.extend(site.and_then(|site| site.location_value()));
            used
        }
        Inst::BinOp { lhs, rhs, .. } | Inst::ICmp { lhs, rhs, .. } => vec![*lhs, *rhs],
        Inst::Select {
            cond,
            then_val,
            else_val,
            ..
        } => vec![*cond, *then_val, *else_val],
        Inst::Call { args, .. } => args.clone(),
        Inst::Return { values } => values.clone(),
        Inst::Br { args, .. } => args.clone(),
        Inst::CondBr {
            cond,
            then_args,
            else_args,
            ..
        } => {
            let mut used = vec![*cond];
            used.extend(then_args.iter().copied());
            used.extend(else_args.iter().copied());
            used
        }
        Inst::Switch {
            value,
            default_args,
            cases,
            ..
        } => {
            let mut used = vec![*value];
            used.extend(default_args.iter().copied());
            for case in cases {
                used.extend(case.args.iter().copied());
            }
            used
        }
        _ => Vec::new(),
    }
}

fn successor_ids(block: &Block) -> Vec<u32> {
    // trust-ir's OWN reading: `body.last().filter(is_terminator)`. A block whose
    // last instruction is not a terminator has no successors here and declines
    // in `collect_edges`; one whose terminator is mid-body is refused before
    // this runs (`reject_misplaced_terminators`).
    block
        .terminator()
        .map(|node| match &node.inst {
            Inst::Br { target, .. } => vec![target.index()],
            Inst::CondBr {
                then_target,
                else_target,
                ..
            } => vec![then_target.index(), else_target.index()],
            Inst::Switch { default, cases, .. } => {
                let mut targets = vec![default.index()];
                targets.extend(cases.iter().map(|case| case.target.index()));
                targets
            }
            _ => Vec::new(),
        })
        .unwrap_or_default()
}

// ---------------------------------------------------------------------------
// Lowering
// ---------------------------------------------------------------------------

impl<'a> Builder<'a> {
    fn build(&mut self) -> Result<(), Decline> {
        self.declare_values()?;
        self.reject_uses_before_definitions()?;
        self.declare_path_conditions();
        self.collect_edges()?;
        self.define_path_conditions();
        for block_id in self.order.clone() {
            self.lower_block(block_id)?;
        }
        Ok(())
    }

    /// Name and type every SSA value the body defines, including block params.
    ///
    /// Names come from `Function.value_names` — the producer's record of the
    /// source binding each value carries — because that is what a contract
    /// clause spells. A value with no recorded name gets `v<id>`, which no
    /// clause can name, so it is reachable only from the body relation.
    ///
    /// Two values that carry the SAME source name (a shadowed `let`) make every
    /// clause mentioning it ambiguous, so the body declines rather than picking
    /// one. That is the shadowing gate, enforced instead of assumed.
    fn declare_values(&mut self) -> Result<(), Decline> {
        let names: BTreeMap<u32, &str> = self
            .function
            .value_names
            .iter()
            .flatten()
            .map(|(value, name)| (value.index(), name.as_str()))
            .collect();
        let mut used: BTreeMap<String, u32> = BTreeMap::new();
        let mut defined: BTreeSet<u32> = BTreeSet::new();
        let function_name = self.function.name.as_str();

        let mut declare = |value: ValueId, ty: &Ty, types: TypeDecoder| -> Result<(), Decline> {
            let sort = types.sort(ty)?;
            // SOUNDNESS (path-local contradiction): one value, one defining
            // equation. A `ValueId` defined twice on the SAME path gets two
            // `pc$b => v == e` assumptions, and two different `e` make that path
            // unsatisfiable — so the solver never explores it and a
            // counterexample living on it disappears. That is a FALSE proof, and
            // it is invisible to the engine's `VacuousTruth` detector, which
            // fires only when the WHOLE assumption set is contradictory. Refused
            // outright rather than modelled: `trust-ir-build`'s `validate_module`
            // rejects a repeated definition too, and this crate does not run it.
            if !defined.insert(value.index()) {
                return Err(Decline::new(format!(
                    "value {} of `{function_name}` is defined more than once: the discharge lane \
                     asserts one defining equation per value under its block's path \
                     condition, and a second definition would make that path \
                     unsatisfiable — erasing every counterexample on it instead of \
                     reporting one",
                    value.index()
                )));
            }
            let name = names
                .get(&value.index())
                .map_or_else(|| format!("v{}", value.index()), ToString::to_string);
            if let Some(what) = reserved_name(&name) {
                return Err(Decline::new(format!(
                    "value {} carries the source name `{name}`, which is reserved for {what}: \
                     the producer's value and the lane's own variable would become ONE unit \
                     variable, and the equation the lane writes over it is not true of the \
                     producer's value",
                    value.index()
                )));
            }
            if let Some(previous) = used.insert(name.clone(), value.index()) {
                if previous != value.index() {
                    return Err(Decline::new(format!(
                        "values {previous} and {} both carry the source name `{name}`, so a \
                         clause naming it would be ambiguous",
                        value.index()
                    )));
                }
            }
            self.values
                .insert(value.index(), ScopeEntry::new(name.clone(), sort.clone()));
            self.relation.variables.insert(name, sort);
            Ok(())
        };

        for block_id in &self.order {
            let block = self.blocks[block_id];
            for (value, ty) in &block.params {
                declare(*value, ty, self.types)?;
            }
            for node in &block.body {
                if let Some(ty) = result_ty(&node.inst, self.module) {
                    let ty = ty?;
                    match node.results.as_slice() {
                        [] => {}
                        [value] => declare(*value, &ty, self.types)?,
                        many => {
                            return Err(Decline::new(format!(
                                "instruction in block {block_id} produces {} results; the \
                                 discharge lane models single-result instructions only",
                                many.len()
                            )))
                        }
                    }
                }
            }
        }

        // The function's own contract scope: the entry formals plus the return
        // place. MEASURED: the clause parser spells `result` as `_0`.
        let entry = self.blocks[&self.function.entry.index()];
        for (value, _) in &entry.params {
            if let Some(entry) = self.values.get(&value.index()) {
                self.relation
                    .scope
                    .insert(entry.emit.clone(), entry.clone());
            }
        }
        if let Some(sort) = self.return_sort()? {
            self.relation
                .variables
                .insert(RESULT_VAR.to_string(), sort.clone());
            self.relation.scope.insert(
                RESULT_VAR.to_string(),
                ScopeEntry::new(RESULT_VAR.to_string(), sort),
            );
        }
        Ok(())
    }

    /// Refuse a value USED before it is defined in the linearized body.
    ///
    /// SOUNDNESS (path-local contradiction), the general case of the duplicate
    /// definition gate. The lane declares every value up front and then relates
    /// them with `pc$b => v == <expr>`, so a definition may textually mention a
    /// value defined later — including ITSELF. `v == v + 1` is unsatisfiable at
    /// every width, so that block's path has no model, the solver never explores
    /// it, and any counterexample living on it is ERASED rather than reported:
    /// the obligation comes back proved over the surviving paths. Two values
    /// defining each other (`a == b + 1`, `b == a + 1`) do the same thing
    /// without either one naming itself, which is why this is a reachability
    /// rule over the whole body and not a self-reference check.
    ///
    /// A valid SSA module always passes: a definition dominates every use, and
    /// in an acyclic CFG a dominator precedes its dominatee in EVERY topological
    /// order (there is a path from it), which is the order `self.order` is in.
    /// So this rejects only modules `trust-ir-build`'s `validate_module` already
    /// rejects — and this crate does not run it, the same hand-built/replayed
    /// bundle threat model `reject_misplaced_terminators` was added under.
    ///
    /// Instructions the lane does not model contribute no operands here; they
    /// decline BY NAME in `lower_block`/`collect_edges`, so nothing they use can
    /// reach the relation.
    fn reject_uses_before_definitions(&self) -> Result<(), Decline> {
        let mut defined: BTreeSet<u32> = BTreeSet::new();
        for block_id in &self.order {
            let block = self.blocks[block_id];
            for (value, _) in &block.params {
                defined.insert(value.index());
            }
            for (index, node) in block.body.iter().enumerate() {
                for used in operand_values(&node.inst) {
                    if !defined.contains(&used.index()) {
                        return Err(Decline::new(format!(
                            "block {block_id} instruction {index} of `{}` (`{}`) uses value {} \
                             before anything on this path defines it: the lane would relate the \
                             two with an equation that can be unsatisfiable (`v == v + 1`), and \
                             an unsatisfiable path is not explored — erasing every \
                             counterexample on it instead of reporting one",
                            self.function.name,
                            inst_name(&node.inst),
                            used.index()
                        )));
                    }
                }
                for result in &node.results {
                    defined.insert(result.index());
                }
            }
        }
        Ok(())
    }

    fn return_sort(&self) -> Result<Option<TrustSort>, Decline> {
        function_return_sort(self.module, self.function, self.types)
    }

    fn declare_path_conditions(&mut self) {
        for block_id in &self.order {
            self.relation
                .variables
                .insert(path_condition(*block_id), TrustSort::Bool);
        }
    }

    fn collect_edges(&mut self) -> Result<(), Decline> {
        for block_id in self.order.clone() {
            let block = self.blocks[&block_id];
            let Some(node) = block.terminator() else {
                return Err(Decline::new(format!(
                    "block {block_id} of `{}` has no terminator: {}",
                    self.function.name,
                    block.body.last().map_or_else(
                        || "the block is empty".to_string(),
                        |node| format!(
                            "its last instruction is `{}`, which is not a terminator",
                            inst_name(&node.inst)
                        )
                    )
                )));
            };
            match &node.inst {
                Inst::Br { target, args } => {
                    self.add_edge(
                        block_id,
                        target.index(),
                        TrustExpr::bool_literal(true),
                        args.clone(),
                    );
                }
                Inst::CondBr {
                    cond,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => {
                    let cond = self.bool_value(*cond, block_id)?;
                    // TWO edges even when `then_target == else_target`: they
                    // carry different guards and may carry different arguments.
                    self.add_edge(
                        block_id,
                        then_target.index(),
                        cond.clone(),
                        then_args.clone(),
                    );
                    self.add_edge(
                        block_id,
                        else_target.index(),
                        TrustExpr::not(cond),
                        else_args.clone(),
                    );
                }
                Inst::Switch {
                    value,
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    let selector = self.value_ref(*value, block_id)?;
                    let mut not_any = Vec::new();
                    let mut seen: Vec<TrustExpr> = Vec::new();
                    for case in cases {
                        let literal = self.constant(&case.value, &selector.1, block_id)?;
                        // SOUNDNESS (path-local contradiction): the case guards
                        // are mutually exclusive ONLY when the case values are
                        // distinct. Two cases carrying the same value make both
                        // arms' path conditions true at once, so their facts
                        // collide (`_0 == 0` and `_0 == 1`), that path has no
                        // model, and the counterexample living on it is erased
                        // instead of reported. trust-ir's interpreter takes the
                        // FIRST matching case, so the program has a perfectly
                        // definite answer here — modelling it would mean
                        // first-match guards, which is new semantics for a shape
                        // `trust-ir-build`'s `validate_module` rejects outright
                        // (`ValidationError::DuplicateSwitchCase`) and this crate
                        // does not run. So it fails closed.
                        if seen.contains(&literal) {
                            return Err(Decline::new(format!(
                                "block {block_id} of `{}` switches on two cases carrying the \
                                 SAME value `{}`: trust-ir takes the first matching case, while \
                                 this lane would make both arms' path conditions true at once \
                                 and their facts contradict — erasing that path instead of \
                                 deciding it",
                                self.function.name, case.value
                            )));
                        }
                        seen.push(literal.clone());
                        self.add_edge(
                            block_id,
                            case.target.index(),
                            TrustExpr::compare(
                                TrustCompareOp::Eq,
                                selector.0.clone(),
                                literal.clone(),
                            ),
                            case.args.clone(),
                        );
                        not_any.push(TrustExpr::compare(
                            TrustCompareOp::Ne,
                            selector.0.clone(),
                            literal,
                        ));
                    }
                    let default_guard = not_any
                        .into_iter()
                        .reduce(|left, right| TrustExpr::logic(TrustLogicOp::And, left, right))
                        .unwrap_or_else(|| TrustExpr::bool_literal(true));
                    self.add_edge(
                        block_id,
                        default.index(),
                        default_guard,
                        default_args.clone(),
                    );
                }
                Inst::Return { .. } => {}
                other => {
                    return Err(Decline::new(format!(
                        "block {block_id} of `{}` ends in `{}`, which the discharge lane does \
                         not model as a terminator",
                        self.function.name,
                        inst_name(other)
                    )))
                }
            }
        }
        Ok(())
    }

    fn add_edge(&mut self, from: u32, to: u32, guard: TrustExpr, args: Vec<ValueId>) {
        self.incoming
            .entry(to)
            .or_default()
            .push(Edge { from, guard, args });
    }

    /// `pc$entry == true`, and every other block's path condition EXACTLY.
    fn define_path_conditions(&mut self) {
        let entry = self.function.entry.index();
        let assumption = TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::variable(path_condition(entry), TrustSort::Bool),
            TrustExpr::bool_literal(true),
        );
        self.assume("pc_entry", assumption);

        for block_id in self.order.clone() {
            if block_id == entry {
                continue;
            }
            let definition = self
                .incoming
                .get(&block_id)
                .map(|edges| {
                    edges
                        .iter()
                        .map(|edge| {
                            TrustExpr::logic(
                                TrustLogicOp::And,
                                TrustExpr::variable(path_condition(edge.from), TrustSort::Bool),
                                edge.guard.clone(),
                            )
                        })
                        .reduce(|left, right| TrustExpr::logic(TrustLogicOp::Or, left, right))
                })
                .unwrap_or(None)
                // A reachable block always has an incoming edge; an empty
                // disjunction is `false`, which is the honest reading anyway.
                .unwrap_or_else(|| TrustExpr::bool_literal(false));
            let assumption = TrustExpr::compare(
                TrustCompareOp::Eq,
                TrustExpr::variable(path_condition(block_id), TrustSort::Bool),
                definition,
            );
            self.assume(&format!("pc_block_{block_id}"), assumption);
        }
    }

    fn lower_block(&mut self, block_id: u32) -> Result<(), Decline> {
        // Block parameters ARE phi nodes: each incoming edge supplies its
        // argument under that edge's own condition.
        let block = self.blocks[&block_id];
        let params = block.params.clone();
        for edge in self.incoming.get(&block_id).cloned().unwrap_or_default() {
            let Edge { from, guard, args } = edge;
            // Checked for EVERY edge, including edges into a block with no
            // parameters: arguments with nothing to bind them to are a
            // shape this lane does not model, and ignoring them would be
            // reading a malformed body as a well-formed one.
            if args.len() != params.len() {
                return Err(Decline::new(format!(
                    "edge {from} -> {block_id} of `{}` passes {} arguments to {} block \
                     parameters",
                    self.function.name,
                    args.len(),
                    params.len()
                )));
            }
            if params.is_empty() {
                continue;
            }
            let edge_taken = TrustExpr::logic(
                TrustLogicOp::And,
                TrustExpr::variable(path_condition(from), TrustSort::Bool),
                guard,
            );
            for ((param, _), arg) in params.iter().zip(args) {
                let param_ref = self.value_ref(*param, block_id)?;
                let arg_ref = self.value_ref(arg, from)?;
                if param_ref.1 != arg_ref.1 {
                    return Err(Decline::new(format!(
                        "edge {from} -> {block_id} of `{}` passes {} to a {} block parameter",
                        self.function.name,
                        arg_ref.1.display_label(),
                        param_ref.1.display_label()
                    )));
                }
                let assumption = TrustExpr::implies(
                    edge_taken.clone(),
                    TrustExpr::compare(TrustCompareOp::Eq, param_ref.0, arg_ref.0),
                );
                self.assume(&format!("phi_{block_id}_{from}"), assumption);
            }
        }

        let body = self.blocks[&block_id].body.clone();
        for (index, node) in body.iter().enumerate() {
            self.lower_inst(block_id, index, &node.inst, &node.results)?;
        }
        Ok(())
    }

    fn lower_inst(
        &mut self,
        block_id: u32,
        index: usize,
        inst: &Inst,
        results: &[ValueId],
    ) -> Result<(), Decline> {
        match inst {
            Inst::Const { ty, value } => {
                let target = self.result_ref(results, block_id)?;
                let literal = self.constant(value, &target.1, block_id)?;
                let _ = ty;
                self.define(block_id, target.0, literal, "const");
            }
            Inst::Copy { operand, .. } => {
                let target = self.result_ref(results, block_id)?;
                let source = self.value_ref(*operand, block_id)?;
                self.define(block_id, target.0, source.0, "copy");
            }
            Inst::BinOp { op, lhs, rhs, .. } => {
                let target = self.result_ref(results, block_id)?;
                let left = self.value_ref(*lhs, block_id)?;
                let right = self.value_ref(*rhs, block_id)?;
                let value = binary(*op, &target.1, left, right, block_id, index)?;
                // The BODY's arithmetic is the machine's: a plain `BinOp::Add`
                // is what a `wrapping_add` (or an overflow-checks-off `+`)
                // lowers to, and modelling it at the declared width is EXACT,
                // not an approximation — a CHECKED add lowers to `Inst::Overflow`,
                // which this lane declines. The premise is disclosure of the
                // width decision, not an excuse for it: it does NOT say the
                // operation cannot overflow, and no clause is read at this width
                // (a mathematical `Formula` node over machine operands declines
                // in the formula decoder).
                if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul)
                    && matches!(target.1, TrustSort::BitVector { .. })
                {
                    self.relation
                        .premises
                        .push(TrustVcNativeTrustIrPremise::new(
                            TrustVcNativeTrustIrPremiseKind::MachineArithmetic,
                            format!(
                            "`{op:?}` at {} in block {block_id} instruction {index} of `{}` is \
                             modelled as the machine's WRAPPING operation at the declared width, \
                             which is what a plain trust-ir `BinOp` denotes; this outcome makes \
                             no claim that it does not overflow",
                            target.1.display_label(),
                            self.function.name
                        ),
                        ));
                }
                self.define(block_id, target.0, value, "binop");
            }
            Inst::UnOp { op, operand, .. } => {
                let target = self.result_ref(results, block_id)?;
                let source = self.value_ref(*operand, block_id)?;
                let value = unary(*op, &target.1, source, block_id, index)?;
                self.define(block_id, target.0, value, "unop");
            }
            Inst::ICmp { op, lhs, rhs, .. } => {
                let target = self.result_ref(results, block_id)?;
                let left = self.value_ref(*lhs, block_id)?;
                let right = self.value_ref(*rhs, block_id)?;
                let value = compare(*op, left, right, block_id, index)?;
                self.define(block_id, target.0, value, "icmp");
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let target = self.result_ref(results, block_id)?;
                let source = self.value_ref(*operand, block_id)?;
                let value = cast(
                    *op,
                    self.types.sort(src_ty)?,
                    self.types.sort(dst_ty)?,
                    source,
                    &target.1,
                    block_id,
                    index,
                )?;
                self.define(block_id, target.0, value, "cast");
            }
            Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            } => {
                let target = self.result_ref(results, block_id)?;
                let cond = self.bool_value(*cond, block_id)?;
                let then_val = self.value_ref(*then_val, block_id)?;
                let else_val = self.value_ref(*else_val, block_id)?;
                // Two guarded equalities rather than a conditional term: the
                // boundary expression has no `Ite`, and this is exactly equal.
                let pc = TrustExpr::variable(path_condition(block_id), TrustSort::Bool);
                self.assume(
                    &format!("select_then_{block_id}_{index}"),
                    TrustExpr::implies(
                        TrustExpr::logic(TrustLogicOp::And, pc.clone(), cond.clone()),
                        TrustExpr::compare(TrustCompareOp::Eq, target.0.clone(), then_val.0),
                    ),
                );
                self.assume(
                    &format!("select_else_{block_id}_{index}"),
                    TrustExpr::implies(
                        TrustExpr::logic(TrustLogicOp::And, pc, TrustExpr::not(cond)),
                        TrustExpr::compare(TrustCompareOp::Eq, target.0, else_val.0),
                    ),
                );
            }
            Inst::Assume { cond } => {
                let cond = self.bool_value(*cond, block_id)?;
                self.assume(
                    &format!("assume_{block_id}_{index}"),
                    TrustExpr::implies(
                        TrustExpr::variable(path_condition(block_id), TrustSort::Bool),
                        cond,
                    ),
                );
                // NEVER silently folded: an `Inst::Assume` is a fact the
                // producer asserted and trust-vc did not prove.
                self.relation
                    .premises
                    .push(TrustVcNativeTrustIrPremise::new(
                        TrustVcNativeTrustIrPremiseKind::BodyAssume,
                        format!(
                            "`Inst::Assume` at block {block_id} instruction {index} of `{}`",
                            self.function.name
                        ),
                    ));
            }
            Inst::Call { callee, args } => {
                self.lower_call(block_id, index, *callee, args, results)?;
            }
            Inst::Return { values } => self.lower_return(block_id, values)?,
            Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } => {}
            Inst::MakeClosure { .. } => {
                return Err(Decline::new(format!(
                    "block {block_id} instruction {index} of `{}` is `MakeClosure`; runtime \
                     closure construction and its ordered live captures are outside the discharge lane",
                    self.function.name
                )))
            }
            // The uniform array `[v; n]`. Its result is an array and the lane
            // has no array sort, so it declines here, by name, rather than
            // through the catch-all below. Neither `ty`, which carries `n`, nor
            // `value` is read, so the decline is the same at every length.
            Inst::ArraySplat { .. } => {
                return Err(Decline::new(format!(
                    "block {block_id} instruction {index} of `{}` is `ArraySplat`, the uniform \
                     array `[v; n]`, which the discharge lane does not model: it has no array \
                     sort",
                    self.function.name
                )))
            }
            other => {
                return Err(Decline::new(format!(
                    "block {block_id} instruction {index} of `{}` is `{}`, which the discharge \
                     lane does not model",
                    self.function.name,
                    inst_name(other)
                )))
            }
        }
        Ok(())
    }

    fn lower_return(&mut self, block_id: u32, values: &[ValueId]) -> Result<(), Decline> {
        let declared = self.return_sort()?;
        match (values, declared) {
            ([], None) => Ok(()),
            ([value], Some(sort)) => {
                let returned = self.value_ref(*value, block_id)?;
                if returned.1 != sort {
                    return Err(Decline::new(format!(
                        "block {block_id} of `{}` returns {} where the signature declares {}",
                        self.function.name,
                        returned.1.display_label(),
                        sort.display_label()
                    )));
                }
                let assumption = TrustExpr::implies(
                    TrustExpr::variable(path_condition(block_id), TrustSort::Bool),
                    TrustExpr::compare(
                        TrustCompareOp::Eq,
                        TrustExpr::variable(RESULT_VAR, sort),
                        returned.0,
                    ),
                );
                self.assume(&format!("return_{block_id}"), assumption);
                Ok(())
            }
            (values, declared) => Err(Decline::new(format!(
                "block {block_id} of `{}` returns {} values but the signature declares {}",
                self.function.name,
                values.len(),
                usize::from(declared.is_some())
            ))),
        }
    }

    /// A call contributes its callee's CONTRACT, never its body.
    ///
    /// Unified compilation makes a callee's body legitimately visible, and using
    /// it definitionally is the superior default — but ONLY for a callee the
    /// producer has positively marked non-opaque, and the pinned trust-ir
    /// carries no such marker (see the module docs). `external_body` is exactly
    /// the case that must stay opaque, and it is indistinguishable here from an
    /// ordinary function. Contract-only is therefore not a policy choice at this
    /// pin, it is the only sound reading — and it is right for `external_body`
    /// in every mode.
    fn lower_call(
        &mut self,
        block_id: u32,
        index: usize,
        callee_id: FuncId,
        args: &[ValueId],
        results: &[ValueId],
    ) -> Result<(), Decline> {
        let callee = self.module.function_by_id(callee_id).ok_or_else(|| {
            Decline::new(format!(
                "block {block_id} instruction {index} of `{}` calls function {}, which is not \
                 in the module",
                self.function.name,
                callee_id.index()
            ))
        })?;

        if self.reaches(callee_id, self.function_id) {
            return Err(Decline::new(format!(
                "call to `{}` is in a recursion cycle with `{}`, or reaches a drop whose glue \
                 the module does not resolve: assuming a callee's `ensures` \
                 to prove that same `ensures` is only sound with a termination measure, and \
                 the pinned trust-ir carries no `decreases`/Termination obligation",
                callee.name, self.function.name
            )));
        }

        let CalleeContractFacts { ensures, omitted } = self.callee_contract_facts(
            callee_id,
            callee,
            CallPosition {
                function: self.function_id,
                block: block_id,
                inst_index: u32::try_from(index).map_err(|_| {
                    Decline::new(format!(
                        "block {block_id} of `{}` has an instruction index that does not fit a \
                         u32, so an `ObligationSite` could never name it",
                        self.function.name
                    ))
                })?,
            },
        )?;
        if !omitted.is_empty() {
            self.relation
                .premises
                .push(TrustVcNativeTrustIrPremise::new(
                    TrustVcNativeTrustIrPremiseKind::UnimportedCalleeObligation,
                    format!(
                        "callee `{}` publishes {} obligation row(s) this lane did not import: \
                         {}. Each omission is an EXPLICIT rule in `callee_contract_facts`, and \
                         each only WEAKENS this unit — a row that could impose an obligation on \
                         the caller declines instead",
                        callee.name,
                        omitted.len(),
                        omitted.join("; ")
                    ),
                ));
        }

        // The callee's contract is written in the callee's own names. Bind them
        // to the caller's argument variables and the call's result variable, so
        // nothing is substituted textually.
        let mut callee_scope = Scope::new();
        let callee_entry = callee
            .blocks
            .iter()
            .find(|block| block.id == callee.entry)
            .ok_or_else(|| {
                Decline::new(format!(
                    "callee `{}` has no entry block, so its parameters cannot be bound",
                    callee.name
                ))
            })?;
        if callee_entry.params.len() != args.len() {
            return Err(Decline::new(format!(
                "call to `{}` passes {} arguments to {} parameters",
                callee.name,
                args.len(),
                callee_entry.params.len()
            )));
        }
        let callee_names: BTreeMap<u32, &str> = callee
            .value_names
            .iter()
            .flatten()
            .map(|(value, name)| (value.index(), name.as_str()))
            .collect();
        for ((param, ty), arg) in callee_entry.params.iter().zip(args) {
            let sort = self.types.sort(ty)?;
            let arg_ref = self.value_ref(*arg, block_id)?;
            if arg_ref.1 != sort {
                return Err(Decline::new(format!(
                    "call to `{}` passes {} to a {} parameter",
                    callee.name,
                    arg_ref.1.display_label(),
                    sort.display_label()
                )));
            }
            let name = callee_names
                .get(&param.index())
                .map_or_else(|| format!("v{}", param.index()), ToString::to_string);
            // The SAME two gates the lowered function's own values get. A
            // callee's contract is rebound onto the caller's variables by NAME,
            // so a name that resolves to two different things resolves to
            // whichever binding was written last — and the clause then asserts
            // something about an argument the callee never named.
            if let Some(what) = reserved_name(&name) {
                return Err(Decline::new(format!(
                    "callee `{}` names parameter {} `{name}`, which is reserved for {what}: \
                     its contract could not be rebound onto the caller without that binding \
                     being overwritten",
                    callee.name,
                    param.index()
                )));
            }
            if callee_scope.contains_key(&name) {
                return Err(Decline::new(format!(
                    "callee `{}` gives two parameters the source name `{name}`, so a clause \
                     naming it would be ambiguous and would bind to whichever caller argument \
                     was written last",
                    callee.name
                )));
            }
            callee_scope.insert(
                name,
                ScopeEntry::new(self.values[&arg.index()].emit.clone(), sort),
            );
        }
        let result_sort = function_return_sort(self.module, callee, self.types)?;
        match (results, &result_sort) {
            ([], None) => {}
            ([value], Some(sort)) => {
                let target = self.values.get(&value.index()).cloned().ok_or_else(|| {
                    Decline::new(format!(
                        "call result {} of `{}` was not declared",
                        value.index(),
                        self.function.name
                    ))
                })?;
                callee_scope.insert(
                    RESULT_VAR.to_string(),
                    ScopeEntry::new(target.emit, sort.clone()),
                );
            }
            _ => {
                return Err(Decline::new(format!(
                    "call to `{}` binds {} results against a {} return",
                    callee.name,
                    results.len(),
                    result_sort.map_or_else(|| "unit".to_string(), |sort| sort.display_label())
                )))
            }
        }

        if ensures.is_empty() {
            // No usable fact at all: the result stays unconstrained. Sound (an
            // unconstrained value proves nothing), and recorded so the caller's
            // outcome says what it rested on.
            self.relation
                .premises
                .push(TrustVcNativeTrustIrPremise::new(
                    TrustVcNativeTrustIrPremiseKind::HavockedCallee,
                    format!(
                        "callee `{}` publishes no postcondition; its result is unconstrained",
                        callee.name
                    ),
                ));
            return Ok(());
        }

        for (obligation, evidence) in ensures {
            let formula = obligation.formula.as_ref().ok_or_else(|| {
                Decline::new(format!(
                    "callee `{}` postcondition {} carries no formula",
                    callee.name,
                    obligation.id.index()
                ))
            })?;
            let node = formula::decode_predicate(formula)?;
            let lowered = FormulaDecoder::new(&callee_scope).lower_predicate(&node)?;
            self.assume(
                &format!(
                    "callee_ensures_{block_id}_{index}_{}",
                    obligation.id.index()
                ),
                TrustExpr::implies(
                    TrustExpr::variable(path_condition(block_id), TrustSort::Bool),
                    lowered,
                ),
            );
            self.relation
                .premises
                .push(TrustVcNativeTrustIrPremise::new(
                    TrustVcNativeTrustIrPremiseKind::CalleeContract,
                    format!(
                        "postcondition {} of callee `{}`, {evidence}, assumed at block \
                     {block_id} instruction {index} (contract-only: the pinned trust-ir carries \
                     no opacity marker, so no callee body is used definitionally)",
                        obligation.id.index(),
                        callee.name,
                    ),
                ));
        }
        Ok(())
    }

    /// # THE INVARIANT OF THIS LANE
    ///
    /// **Opaque evidence and status labels are not proof authority.** That is
    /// upstream trust-ir's own wording, for the error it raises when a consumer
    /// tries the opposite, and it is this lane's contract. Concretely: NO claim
    /// a producer makes about whether something was proved is authority for
    /// anything here. For every obligation, the lane either
    ///
    ///   (a) PROVES it from the body with its own encoder and ay,
    ///   (b) accepts a certificate that was RE-CHECKED in this process — the
    ///       `Certified` tier, whose `CleanCic` term `validate_producer_module`
    ///       re-runs through the Clean kernel before the lane ever sees the
    ///       module — or
    ///   (c) DECLINES.
    ///
    /// A [`ProofStatus`] value is a LABEL, not evidence, and must never by
    /// itself license assuming a fact. Adversarial review rounds 1-6 each found
    /// one false `Discharged` on this lane; rounds 5 and 6 found them at THIS
    /// seam, and round 6's two were both created by round 5's own fix. The
    /// enumeration below exists so round 9 does not have to rediscover it.
    ///
    /// AND THE INVARIANT RUNS IN BOTH DIRECTIONS — round 8. It is not only about
    /// what this lane believes; it is about what it PUBLISHES. An assertion id
    /// stamped onto a released artifact is a claim that a specific source-level
    /// assertion was proved, and until round 8 that id came from ONE producer
    /// field with nothing compared against it. Everything E1-E25 covers is the
    /// import side; E26 and [`crate::native_assertion_id`] are the export side.
    ///
    /// # EVERY POINT WHERE A PRODUCER CLAIM CAN INFLUENCE A VERDICT
    ///
    /// Enumerated on purpose rather than one-at-a-time by accident. "HOLDS"
    /// means the invariant holds there.
    ///
    /// ## Bundle / request layer (`native_trust_ir_bundle.rs`), before the lane
    ///
    /// * **P1 · the whole module** — `validate_producer_module` runs
    ///   `trust_ir_build::validate_module` as an INPUT GATE. Every error refuses
    ///   except the one carve-out below; `ValidationError` is `#[non_exhaustive]`
    ///   so an unknown upstream variant refuses by default. HOLDS.
    /// * **P2 · the carve-out** — `is_proof_replay_capability_verdict` carries
    ///   `DischargedWithoutCertificate` past. At the pinned rev that verdict
    ///   fires for EVERY `Discharged` row with no authority-admitted
    ///   certificate, i.e. unconditionally under the rejecting authority this
    ///   crate passes. It is load-bearing for the IMPORT/MERGE GRADING path (the
    ///   CLI acceptance fixture moves obligation 0 to `Discharged`), so it
    ///   stays — SCOPED: it means "this crate grades certificates itself", never
    ///   "a `Discharged` label is established". Everything downstream must treat
    ///   `Discharged` as UNBACKED. Round 6, blocker 1.
    /// * **P3 · `MissingTrustVcEvidenceForObligation`** —
    ///   `is_discharge_mode_certificate_rule` relaxes it for a discharge
    ///   request's own obligations. It is about the request's INPUT evidence and
    ///   says nothing about the answer. HOLDS.
    /// * **P4 · `request.mode`** — selects which arm mints the verdict; each arm
    ///   can only mint its own verdicts (`build_request_report`). HOLDS.
    /// * **P5 · `request.certificates` → `TrustVcNativeTrustIrCertificateAdmission`**
    ///   — METADATA-ONLY grading (assertion id, suite/solver identity, transcript
    ///   and compiler-fact digests, and the obligation's STATUS LABEL). It admits
    ///   on a bare `Discharged`. Correct for its job, which is grading an import;
    ///   NOT proof authority, which is exactly why the gate below does not route
    ///   through it. On the discharge lane the request's input certificates are
    ///   dropped from `proof_evidence` entirely. HOLDS for grading.
    /// * **P6 · `PublicObligationIdentity.obligation_id`** — a producer-chosen
    ///   string used as the unit id and certificate key (`unit_id_for`).
    ///   Identity only; it licenses no fact. HOLDS.
    /// * **P7 · `PublicObligationIdentity.semantic_digest`** — copied verbatim
    ///   onto a produced certificate and labelled THE PRODUCER'S CLAIM, beside
    ///   `formula_payload_sha256`, which this crate computes over the bytes it
    ///   actually decided. Not conflated. HOLDS.
    ///
    /// ## The lane (`native_discharge`)
    ///
    /// * **E1 · `request.function`** — positively required; absent or unresolved
    ///   refuses the request. HOLDS.
    /// * **E2 · `obligation.function` on the REQUESTED row** — must positively
    ///   equal the request's function; `None` declines rather than being decided
    ///   against whatever body the request happened to name. HOLDS.
    /// * **E3 · `obligation.site` on the REQUESTED row** — trust-ir requires
    ///   every row a discharge request cites to be sited in the requested
    ///   function. A `Postcondition` sited at the function's ONE `Return`
    ///   terminator is decided (the lane checks it at every return, which is
    ///   that one); any other site DECLINES, including a function with several
    ///   returns. Fail-closed. HOLDS.
    /// * **E4 · `obligation.kind` on the REQUESTED row** — only `Postcondition`
    ///   is decided; `Precondition` declines, and the `ref other` arm declines
    ///   every present and future variant. HOLDS.
    /// * **E5 · the function's own def-site `requires` selection**
    ///   (`discharge_request`) — `function == Some(f) && site.is_none() && kind
    ///   == Precondition`. This filter has the SAME SHAPE as the fail-open one
    ///   below and is nonetheless safe, for a reason worth stating: a row it
    ///   drops REMOVES an assumption, which makes the unit STRICTLY STRONGER, so
    ///   a drop can only over-reject. A row it wrongly ADDED would be the
    ///   danger, and it adds only def-site preconditions, which is what a
    ///   `requires` MEANS. A `requires` it cannot lower refuses the request
    ///   rather than being dropped. HOLDS — and the asymmetry is why the
    ///   callee-side filter needed the opposite default.
    /// * **E6 · `ProofStatus` of the function's own `requires`** — deliberately
    ///   NOT READ. A def-site `requires` is what the CALL SITES owe; its status
    ///   says nothing about whether assuming it at the definition site is sound.
    ///   HOLDS.
    /// * **E7 · the precondition scope** — a def-site `requires` is lowered
    ///   against the entry formals ONLY (`relation.scope` is entry params plus
    ///   `_0`, minus `_0`), so a `requires` naming the return place is
    ///   unresolvable rather than pinning a value the program never computes.
    ///   HOLDS.
    /// * **E8 · `obligation.formula.schema` / `.payload`** — decoded, never
    ///   trusted: an unknown schema or node declines BY NAME, a variable not in
    ///   scope declines, and a wire sort that disagrees with the declared sort
    ///   declines. HOLDS. The OTHER two fields of the same struct are E19 and
    ///   E20 — round 7 found them missing from this list, and one of them was a
    ///   live divergence.
    /// * **E9 · `Inst::Call { callee }`** — must resolve to a function in the
    ///   module, and a call in a recursion cycle declines (assuming an `ensures`
    ///   to prove that same `ensures` needs a termination measure the pin does
    ///   not carry). HOLDS.
    /// * **E10 · THE CALLEE CONTRACT ROW SELECTION — this function.** Was
    ///   `function == Some(callee) && site.is_none() && kind in {Pre, Post}`.
    ///   FAIL-OPEN (round 6, blocker 2): a `Precondition` carrying a SITE never
    ///   entered the collection the `assume(P) |- P` guard scanned, so the
    ///   `requires` was silently dropped and the `ensures` assumed
    ///   unconditionally — on a claim false at `x = 0`. Round 6 inverted the
    ///   `site` half and left `.filter(|o| o.function == Some(callee))` in
    ///   place, which is the SAME silent pre-filter one field over, and round 7
    ///   exploited it: upstream checks scope/site agreement only "when both are
    ///   present", so a `Precondition` with `function: None` sited INSIDE the
    ///   callee is well-formed and was never adjudicated. NOW: attribution over
    ///   BOTH fields ([`RowAttribution`]), the only positive exclusion being "the
    ///   producer named a function and it is not this callee"; an UNATTRIBUTED
    ///   row is adjudicated for refusal and is never a source of an imported
    ///   fact; then an explicit, justified rule per kind, and an
    ///   `#[non_exhaustive]` catch-all that DECLINES. HOLDS — with round 8's
    ///   correction: what closed round 7's exploit was the separate
    ///   `Unattributed` arm, NOT "attribution over BOTH fields". Measured in
    ///   round 8: the `site.function` half of [`RowAttribution::of`] changed no
    ///   outcome on any shape the input gate admits, and through the product
    ///   entry point its only effect was to make the lane MORE permissive. It is
    ///   kept because it performs a real POSITIVE exclusion (a row sited in a
    ///   third function at an instruction that is not a call to this callee),
    ///   and that exclusion now has a discriminating test of its own. E25 is the
    ///   rule that does the guarding.
    /// * **E10a · `obligation.kind` on a CALLEE row** — every kind has a written
    ///   rule. `Precondition`, `RefinementType` and `TypeInvariant` REFUSE
    ///   (round 7: over a scalar parameter a refinement is indistinguishable
    ///   from a caller-owed constraint, and "it is callee-own" was assertion,
    ///   not argument). The rest are omitted with the argument recorded at the
    ///   arm. An unknown kind refuses. HOLDS.
    /// * **E11 · `ProofStatus` of an imported callee `ensures`** —
    ///   `established_callee_ensures`. Was `Discharged | Certified`. FAIL-OPEN
    ///   (round 6, blocker 1): `Discharged` is exactly the label P2 lets through
    ///   with nothing behind it. NOW: `Certified` ONLY, plus a lineage-bound
    ///   non-empty `CleanCic` certificate in the module — and the gate RETURNS
    ///   the words the `CalleeContract` premise prints, so the premise cannot
    ///   assert evidence the gate did not test (round 7: it hard-coded
    ///   "with a lineage-bound `CleanCic` certificate" and still printed it with
    ///   the gate neutralized). HOLDS.
    /// * **E12 · `module.proof_certificates`** — read here ONLY for the lineage
    ///   binding, which upstream is explicit is NOT an admissibility gate. The
    ///   authority is P1's `validate_certified_evidence_with_catalog`, which
    ///   re-grounds the goal from the obligation and type-checks the term in the
    ///   Clean kernel IN THIS PROCESS, and which is NOT carved out. HOLDS.
    ///   MEASURED, and load-bearing for E19: that re-check is
    ///   `trust_ir_build::validate::contract_clean_cic_rechecks`, compiled in
    ///   because this crate takes `trust-ir-build` with its default features
    ///   (`clean-tv-anchor` among them; basis-K coverage needs it too). At this
    ///   pin trust-ir grounds a contract only from an `smtlib2` formula, which
    ///   the decoder here does not read, so no `Certified` contract row this
    ///   lane could import can be minted, and E19's one-rendering rule declines
    ///   any row that carries two texts (pinned end to end by
    ///   `a_certified_callee_contract_cannot_be_minted_at_this_pin`).
    /// * **E13 · `callee.value_names`** — the producer's names, through which a
    ///   callee clause is rebound onto caller arguments. A reserved name or a
    ///   duplicate declines rather than silently binding to whichever came last.
    ///   HOLDS.
    /// * **E14 · callee entry block, parameter arity and sorts, result arity** —
    ///   positively checked; any mismatch declines. HOLDS.
    /// * **E15 · `Inst::Assume` in the body** — the producer's own assumption,
    ///   folded in. DOES NOT HOLD, BY DESIGN, and that is why it is published as
    ///   a [`TrustVcNativeTrustIrPremiseKind::BodyAssume`] premise: an assume IS
    ///   the producer speaking, and a false one kills the path carrying the
    ///   counterexample. Recorded, never silent.
    /// * **E16 · `module.target_info.pointer_size`** — a producer fact setting
    ///   the `usize`/`isize` width; an unusable value declines rather than
    ///   defaulting to the host's. HOLDS.
    /// * **E17 · proof-artifact binding** (`unit::decide`) — the artifact must
    ///   carry THIS assertion's id; no first-match fallback, and a refutation
    ///   labelled with someone else's assertion becomes `NotProved`, never a
    ///   counterexample attributed here. HOLDS.
    /// * **E18 · certificate minting** — `decided.proof.filter(|_| verified)`:
    ///   a certificate is minted only from this lane's own `Verified` solve.
    ///   HOLDS.
    /// * **E19 · `obligation.formula.smtlib` — THE SECOND RENDERING.** Round 7's
    ///   missed entry, and it falsified the authority claim E11/E12 make. A
    ///   [`trust_ir::ProofFormula`] carries `payload` AND an optional `smtlib`;
    ///   this lane decoded only `payload`, while the Clean-kernel re-check that
    ///   is E11's authority grounds its goal from
    ///   `clean_expr_lowering::contract::predicate_text`, i.e.
    ///   `smtlib.unwrap_or(payload)` — it PREFERS `smtlib`. Nothing upstream
    ///   binds them: `clean_cic_lineage_digest` hashes both but never compares
    ///   them, so a closed tautology in `smtlib` mints a REAL certificate while
    ///   `payload` says something else entirely (measured: `(>= _0 0)` against
    ///   `_0 >= 100`). NOW a rule at the single decode seam,
    ///   `formula::decode_predicate`: `smtlib` absent, or byte-identical to
    ///   `payload`, or DECLINE — applied to every predicate the lane reads (the
    ///   one it decides, the `requires` it assumes, the `ensures` it imports),
    ///   because a divergence misidentifies the formula rather than misusing one
    ///   role of it. HOLDS. DISCLOSED COST: under schema
    ///   `trust-types.Formula@1` the payload is a JSON document and a
    ///   kernel-groundable predicate is SMT-LIB text, so no row can be both
    ///   kernel-certifiable and decodable here — the E11 import path is now
    ///   structurally unreachable end-to-end, not merely feature-gated off. The
    ///   remedy is upstream (one rendering, or a binding between the two), not a
    ///   semantic comparison of two notations invented in this crate. The rule
    ///   also repairs `formula_payload_sha256` on every produced certificate and
    ///   outcome: it hashes `payload`, which is now guaranteed to be THE
    ///   rendering of the formula this lane decided rather than one of two.
    /// * **E20 · `obligation.formula.sort`** — NOT READ by this LANE, and
    ///   authority for nothing that gates it: neither `predicate_text` nor
    ///   `contract_goal` consults it, and every variable's sort here is resolved
    ///   from the DECLARED trust-ir signature, with a specific wire sort
    ///   required to AGREE with the declaration (E8). Listed because round 7's
    ///   finding was that an unlisted producer field is an unexamined one.
    ///   HOLDS.
    ///
    ///   CORRECTED, round 8: "NOT READ" was true of the LANE and FALSE of the
    ///   CRATE. `evidence_row` copies `formula.sort`, `formula.schema` and
    ///   `obligation.description` VERBATIM onto every produced evidence row.
    ///   They gate nothing, and they are republished as the producer's own
    ///   words — but "this crate does not read it" was the wrong sentence, and
    ///   it is exactly the class of claim that put the export seam outside
    ///   round 7's enumeration. The authority for "who reads what" is now the
    ///   DERIVED table in [`crate::producer_fields`], which scans the whole
    ///   crate and fails a test when a field gains a read site.
    /// * **E21 · `obligation.id`** — the producer's `ProofId`, used to FIND a
    ///   row (`lower_predicate`, the def-site `requires` selection), to key the
    ///   outcome, and to name it in a decline. Identity only; it licenses no
    ///   fact. Two rows sharing an id would let a linear `find` and a keyed map
    ///   disagree about which formula was decided — `validate_module` rejects a
    ///   duplicate `ProofId`, and P1 makes that an input gate. HOLDS.
    /// * **E22 · `obligation.source.public.obligation_id`** — the `vc:…` public
    ///   identity, taken verbatim as the unit id (`unit_id_for`) and, when
    ///   absent, replaced by a spelling that cannot be confused with one. This
    ///   is the producer NAMING the row a consumer joins on; it decides nothing.
    ///   HOLDS (and see P6/P7 for the same string at the bundle layer).
    /// * **E23 · `function.ty` / `callee.ty` → `module.func_types`** — the
    ///   DECLARED signature, which is where every sort in this lane comes from
    ///   (E8's "declared scope", E14's arity check, `function_return_sort`). A
    ///   `ty` index not in the module declines; a signature that disagrees with
    ///   the entry block declines. It is a producer fact and the lane has no
    ///   independent source for it — the same standing as E16's
    ///   `target_info.pointer_size`, and recorded on the same terms. HOLDS.
    /// * **E24 · `function.name` / `callee.name`** — producer strings, used in
    ///   messages, in premise text and as the `requires` assumption-name prefix.
    ///   Never used to RESOLVE a callee (that is `FuncId`, E9), which is what
    ///   round 2's callee-name ambiguity finding was about. HOLDS.
    ///
    /// * **E25 · `obligation.site` AT A CALL INSTRUCTION — ROUND 8, MAJOR 1.**
    ///   A `Precondition` anchored at the call is the DOCUMENTED shape of a
    ///   call-site VC, and it lives in the CALLER: both `function` and
    ///   `site.function` name the caller, so the row was classified
    ///   `AnotherFunction`, skipped BEFORE adjudication, never used as a guard,
    ///   never recorded in the `UnimportedCalleeObligation` premise, and never
    ///   discharged (E3 declines every sited row as a REQUESTED row). Nobody
    ///   owed it, and the callee's `ensures` was imported UNGUARDED. NOW one
    ///   POSITIVE rule, checked FIRST so it overrides `function`: a row whose
    ///   `site` resolves to an instruction that CALLS this callee is this
    ///   callee's, and a site that resolves to no direct call (a missing
    ///   instruction, or a `CallIndirect`, which names no callee) is adjudicated
    ///   rather than excluded. HOLDS.
    /// * **E26 · THE EXPORT SEAM — ROUND 8, THE BLOCKER — is NOT in this lane
    ///   and that is why it was missed.** Everything E1-E25 covers is what the
    ///   lane IMPORTS. What it PUBLISHES is stamped in
    ///   `native_trust_ir_bundle.rs`, from
    ///   `compiler_facts.obligation_sources[].assertion_id` — a producer field
    ///   this directory never touches. The bundle carries three other renderings
    ///   of that identity and nothing compared them. See
    ///   [`crate::native_assertion_id`], and see [`crate::producer_fields`] for
    ///   why an enumeration scoped to a DIRECTORY could not have found it.
    ///
    /// # How to check this list is still COMPLETE
    ///
    /// Do not re-read it and agree with it, and do not grep this directory —
    /// that is precisely the recipe that stood here through round 7 and could
    /// never have found the export seam, because the seam is in another file and
    /// reads a receiver that was not one of the six names it matched.
    ///
    /// The authority is [`crate::producer_fields`]: a table DERIVED from the
    /// producer types (a compile-time exhaustive destructuring of each one, so
    /// an upstream field addition breaks the build) and from a scan of the WHOLE
    /// crate (a test that fails when any producer field gains or loses a read
    /// site). E1-E26 are the ARGUMENT about the entries that gate a verdict; the
    /// table is the CENSUS, and the census is the part that cannot go stale.
    ///
    /// # What this function does
    ///
    /// Adjudicates EVERY row that could be `callee_id`'s — no pre-filter on any
    /// producer field — and returns the def-site `ensures` rows the lane may
    /// assume, plus a record of what it deliberately did not import. A row is
    /// INCLUDED by default; it is excluded only by a rule written here, and a
    /// kind with no rule DECLINES the call.
    ///
    /// ## "Could be this callee's" — ROUND 7, blocker 2 AS A CLASS
    ///
    /// Round 6 inverted the `site` filter. `function` was still a silent
    /// pre-filter (`obligation.function == Some(callee_id)`), which is the same
    /// shape one field over, and upstream leaves the gap open on purpose:
    /// `validate_obligation_sites` checks scope/site agreement only "when both
    /// are present", so a `Precondition` with `function: None` and an
    /// [`ObligationSite`] pointing at a real instruction INSIDE the callee is
    /// WELL-FORMED to the producer validator. It never entered the adjudication,
    /// the `requires` was dropped in silence, and the `ensures` was imported
    /// unguarded. Measured, round 7 probe R7-P1.
    ///
    /// Attribution is now [`RowAttribution`], over BOTH fields, and it is
    /// exclusion that must be positive:
    ///
    /// * `function` or `site.function` names this callee → the row is ADJUDICATED.
    /// * at least one of them is set and neither names this callee → the row is
    ///   positively SOMEONE ELSE'S, and only then is it skipped.
    /// * neither is set → UNATTRIBUTED. The producer said nothing about whose
    ///   row it is, so it cannot be excluded from being this callee's. It is
    ///   adjudicated for REFUSAL but is never a source of an imported fact:
    ///   treating an unattributed `ensures` as the callee's would be the same
    ///   fail-open move in the other direction.
    ///
    /// # The measured cost, disclosed rather than smoothed over
    ///
    /// A callee carrying ANY `Precondition` row — including a per-check
    /// call-site VC of its own body — declines at every call, and so does any
    /// call in a module carrying an unattributed `Precondition` anywhere. There
    /// is no marker at this pin that separates a published `requires` from an
    /// instruction-anchored VC, and a heuristic that guessed (for example "a
    /// site pointing at a `Call` is internal") is defeated by a producer that
    /// anchors the real `requires` at a call.
    ///
    /// ROUND 8 WIDENS THAT COST. A call-site `Precondition` anchored at ANY call
    /// to this callee now declines too, wherever in the module that call is
    /// (E25). MEASURED over both feature sets of this crate's suites: zero
    /// additional rejections — no fixture and no test carries such a row, so the
    /// whole measured cost of E25 is on shapes that were previously a false
    /// import.
    ///
    /// The principled remedy is NOT a better filter: it is to stop needing one,
    /// by importing the callee's contract as the IMPLICATION it actually is —
    /// assume `(/\ every precondition attributable to the callee) => ensures`
    /// instead of `ensures`.
    ///
    /// ROUND 8, AND THIS IS WHY THE REMEDY IS NOT WRITTEN THE WAY IT STOOD HERE:
    /// "attributable to the callee" was meant in the [`RowAttribution`] sense,
    /// and under that sense a CALLER-scoped call-site precondition is
    /// attributable to the CALLER. The conjunction would have been EMPTY for
    /// exactly the row E25 is about, the guard would have been `true`, and the
    /// remedy would have shipped the same false import it was meant to close.
    /// Any future version of it must range over "every precondition this call is
    /// answerable for" in the E25 sense — including a row anchored at THIS call
    /// whatever it is scoped to — and must still refuse when a row it cannot
    /// lower would have belonged in the conjunction. Recorded as the next step,
    /// with that correction attached to it.
    fn callee_contract_facts(
        &self,
        callee_id: FuncId,
        callee: &Function,
        call: CallPosition,
    ) -> Result<CalleeContractFacts<'a>, Decline> {
        let mut ensures = Vec::new();
        let mut omitted = Vec::new();
        for obligation in self.module.proof_obligations.iter() {
            let attribution = RowAttribution::of(obligation, callee_id, self.module, call);
            // THE ONLY EXCLUSION THAT HAPPENS BEFORE ADJUDICATION, and it is a
            // POSITIVE one: the producer named a function, and it is not this
            // callee. Everything else is adjudicated below.
            if attribution == RowAttribution::AnotherFunction {
                continue;
            }
            let id = obligation.id.index();
            let whose = attribution.phrase(&callee.name);
            match obligation.kind {
                // OWED BY THE CALLER, at ANY site, ANY scope and ANY status.
                // Discharging a call-site precondition is a separate obligation
                // this slice does not decide, and ASSUMING it is the
                // `assume(P) |- P` false accept. Neither `site` nor `function`
                // is consulted to drop it: those were the round-6 and round-7
                // bypasses, one field apart.
                ObligationKind::Precondition => {
                    return Err(Decline::new(format!(
                        "precondition {id} is {whose} ({}); discharging a call-site \
                         precondition is a separate obligation this slice does not decide, and \
                         ASSUMING it would be the `assume(P) |- P` false accept",
                        match obligation.site {
                            Some(site) => format!(
                                "anchored at block {} instruction {} — a SITE does not make a \
                                 `requires` droppable",
                                site.block.index(),
                                site.inst_index
                            ),
                            None => "def-site".to_string(),
                        }
                    )))
                }
                // ROUND-7 MINOR: a refinement or a type invariant over a SCALAR
                // parameter is reachable in a call this lane models, and nothing
                // at this pin says whether it constrains the callee's own values
                // or the arguments its callers must pass. A producer that spells
                // a caller-owed constraint as one of these rather than as a
                // `Precondition` would otherwise get the `ensures` imported
                // unguarded — the same fail-open direction, one kind over. The
                // previous rule omitted both on an ASSERTION that they are
                // callee-own; there is no argument for that here, so they
                // refuse.
                ObligationKind::RefinementType | ObligationKind::TypeInvariant => {
                    return Err(Decline::new(format!(
                        "{:?} obligation {id} is {whose}, and this lane cannot tell a refinement \
                         on the callee's OWN values from one the CALLER must establish about the \
                         arguments it passes: over a scalar parameter both readings are \
                         well-formed, so it is refused rather than assumed away",
                        obligation.kind
                    )))
                }
                // THE ONE IMPORTABLE SHAPE: a def-site `ensures` the producer
                // POSITIVELY scoped to this callee. An UNATTRIBUTED postcondition
                // falls through to the omission arm below — importing it would
                // be the same fail-open move as dropping an unattributed
                // `requires`, in the other direction.
                ObligationKind::Postcondition
                    if obligation.site.is_none() && attribution == RowAttribution::ThisCallee =>
                {
                    let evidence = self.established_callee_ensures(callee, obligation)?;
                    ensures.push((obligation, evidence));
                }
                // An instruction-anchored postcondition is a per-check VC of the
                // callee's own body, not its published contract; an unattributed
                // one is not known to be this callee's contract at all. OMITTING
                // either only leaves the call's result less constrained, so the
                // omission can never strengthen this unit — but it is RECORDED
                // rather than dropped in silence.
                ObligationKind::Postcondition => omitted.push(format!(
                    "postcondition {id} ({})",
                    match (attribution, obligation.site) {
                        (RowAttribution::Unattributed, _) => format!(
                            "attributed to no function, so it is not known to be `{}`'s \
                             published contract",
                            callee.name
                        ),
                        (_, Some(_)) => format!(
                            "anchored at an instruction site — a per-check VC of `{}`, not its \
                             published contract",
                            callee.name
                        ),
                        // Not reachable: a `ThisCallee` def-site postcondition is
                        // the importable arm above. Spelled as a STRING rather
                        // than `unreachable!()` so that a future edit to that
                        // arm turns into a visible omission rather than a panic
                        // in a soundness-critical path.
                        (_, None) => format!(
                            "def-site row of `{}` that the import arm did not take",
                            callee.name
                        ),
                    }
                )),
                // Claims about the CALLEE'S OWN execution or compilation, none of
                // which the caller establishes and none of which is a fact about
                // the call's result, so omitting each only weakens this unit.
                //
                // The argument, per group. `LoopInvariant` and
                // `TranslationValidation` are about the callee's body and its
                // lowering. The panic classes (`PanicFreedom`,
                // `ArithmeticSafety`, `BoundsCheck`) and `TemporalSafety` /
                // `Liveness` are total-correctness claims: an unproved one means
                // the call may not return, which can only make a path INFEASIBLE,
                // and keeping an infeasible path is an over-approximation this
                // unit must still prove on. `MemorySafety` and
                // `GiveBackRefinement` are additionally unreachable in a call
                // this lane models at all — every pointer, reference and
                // aggregate type declines in `TypeDecoder::sort`, at the callee's
                // parameters and at its return.
                //
                // `RefinementType` and `TypeInvariant` were in this list until
                // round 7 and are NOT: see the refusal arm above.
                ObligationKind::LoopInvariant
                | ObligationKind::TranslationValidation
                | ObligationKind::MemorySafety
                | ObligationKind::PanicFreedom
                | ObligationKind::TemporalSafety
                | ObligationKind::Liveness
                | ObligationKind::ArithmeticSafety
                | ObligationKind::BoundsCheck
                | ObligationKind::GiveBackRefinement => {
                    omitted.push(format!("{:?} {id} ({whose})", obligation.kind));
                }
                // `ObligationKind` is `#[non_exhaustive]`. A row whose meaning
                // this build does not know may be one the CALLER owes, so it
                // refuses rather than being silently dropped — a filter that
                // drops what it does not understand is fail-open by
                // construction, which is the class rounds 6 and 7 were about.
                ref other => {
                    return Err(Decline::new(format!(
                        "obligation {id} of kind `{other:?}` is {whose}, and this lane has no \
                         rule for it: a row whose meaning is unknown may be the caller's to \
                         discharge, so it is refused rather than dropped"
                    )))
                }
            }
        }
        Ok(CalleeContractFacts { ensures, omitted })
    }

    /// THE STATUS + EVIDENCE GATE for the one fact this lane IMPORTS rather than
    /// derives (invariant point E11, and round 6's blocker 1).
    ///
    /// `Certified` ONLY — and the rejected alternative is worth recording.
    /// `Discharged` was accepted until round 6. It cannot be: at the pinned rev
    /// `validate_discharged_authority` reports every `Discharged` row with no
    /// authority-admitted certificate, this crate passes the REJECTING
    /// authority, and `validate_producer_module` carries exactly that verdict
    /// past its gate. So `Discharged` here is a bare label with nothing behind
    /// it, and upstream says so in the error's own words: "status is Discharged
    /// but no exact certificate was replayed by this validator — opaque evidence
    /// and status labels are not proof authority".
    ///
    /// The OTHER candidate — "a certificate this crate's own admission path
    /// accepts" — was examined and is WRONG here.
    /// [`TrustVcNativeTrustIrCertificateAdmission::from_native_parts`] grades
    /// METADATA: an assertion id, a suite and solver identity, a transcript
    /// digest, compiler-fact digests, and the obligation's STATUS. It runs no
    /// kernel and re-checks no proof term, and it ADMITS on `Discharged`. Routing
    /// this gate through it would have accepted precisely the shape the probe
    /// exploits. It is the right grader for an IMPORT; it is not evidence.
    ///
    /// What makes `Certified` different is that something really is re-checked,
    /// in this process, before the lane runs:
    /// `trust_ir_build::validate_module` (the P1 input gate) calls
    /// `validate_certified_evidence_with_catalog`, which for every `Certified`
    /// row requires a `CleanCic` certificate with a NON-EMPTY term whose lineage
    /// digest matches the obligation, and then re-grounds the goal FROM THE
    /// OBLIGATION and has the Clean kernel type-check the decoded term against
    /// it. `CertifiedWithoutCleanCic`, `CertifiedCleanCicLineageMismatch` and
    /// `CertifiedCleanCicKernelRecheckFailed` are all FATAL here — none is
    /// carved out (round 5 removed the last one that was).
    ///
    /// The lineage check below is DEFENCE IN DEPTH, not the authority: upstream
    /// is explicit that a lineage match is an identity helper and "not an
    /// admissibility gate". It is here so that this seam refuses a `Certified`
    /// label with no certificate at all on its own terms, without depending on
    /// a gate one layer up that a future refactor could route around.
    ///
    /// RETURNS THE EVIDENCE IT CHECKED, as the words the `CalleeContract`
    /// premise prints. Round 7 found the premise hard-coding "with a
    /// lineage-bound `CleanCic` certificate" and the status label separately, so
    /// with this gate neutralized in place the premise still claimed a
    /// certificate for a row that had none. A premise must be a report of a
    /// check, not a parallel assertion about it.
    fn established_callee_ensures(
        &self,
        callee: &Function,
        obligation: &ProofObligation,
    ) -> Result<String, Decline> {
        if obligation.status != ProofStatus::Certified {
            return Err(Decline::new(format!(
                "callee `{}` publishes postcondition {} at proof status `{:?}`, and only \
                 `Certified` is EVIDENCE on this lane: `Pending` is unproved, `Failed` is \
                 refuted, `Trusted` is faith, and `Discharged` is a LABEL the producer \
                 validator lets through with no certificate behind it at all — opaque evidence \
                 and status labels are not proof authority",
                callee.name,
                obligation.id.index(),
                obligation.status
            )));
        }
        // ROUND 8, MINOR: the premise must carry a value DERIVED from this
        // check, not a SENTENCE about it. Round 7 moved the claim out of the
        // premise and into this function, which is where it belongs — but the
        // text it returned was still composed AFTER the check and carried
        // nothing the check produced, so under neutralization it went on
        // asserting a lineage-bound kernel-rechecked `CleanCic` certificate for
        // a row that had none. The certificate is therefore FOUND here (the
        // same predicate `obligation_has_matching_clean_cic` applies, spelled
        // out so the matching row can be named), and the premise quotes its
        // lineage digest and the digest of its term. Delete the search and
        // there is nothing to print.
        let expected_lineage = trust_ir::proof::clean_cic_lineage_digest(obligation);
        let established = self
            .module
            .proof_certificates
            .iter()
            .find_map(|certificate| match &certificate.evidence {
                trust_ir::ProofEvidence::CleanCic { term, lineage, .. }
                    if certificate.obligation == obligation.id
                        && !term.is_empty()
                        && *lineage == expected_lineage =>
                {
                    Some((certificate, term, lineage))
                }
                _ => None,
            });
        let Some((certificate, term, lineage)) = established else {
            return Err(Decline::new(format!(
                "callee `{}` publishes postcondition {} at `Certified` with no lineage-bound, \
                 non-empty `CleanCic` certificate in the module: the status is a label, and the \
                 certificate is what the producer validator re-checks in the Clean kernel \
                 (expected lineage {expected_lineage})",
                callee.name,
                obligation.id.index()
            )));
        };
        debug_assert!(trust_ir::proof::obligation_has_matching_clean_cic(
            obligation,
            &self.module.proof_certificates,
        ));
        Ok(format!(
            "at producer proof status `{}`, established by `CleanCic` certificate \
             {certificate_digest} from prover `{prover}`: lineage {lineage}, which equals \
             `clean_cic_lineage_digest` of THIS row, over a {term_len}-byte term \
             sha256:{term_digest}. That term is what the producer validator re-checked in the \
             Clean kernel at the input gate; these digests are read off the certificate this \
             check matched, so a premise cannot outlive the check that produced it",
            obligation.status,
            certificate_digest = certificate.stable_digest(),
            prover = certificate.prover,
            term_len = term.len(),
            term_digest = crate::native_trust_ir_bundle::sha256_hex(term),
        ))
    }

    /// Does `from` reach `to` through direct calls inside this module?
    ///
    /// A direct call is every instruction [`direct_callee`] names a function
    /// for, whatever its unwind shape. A drop whose glue does not resolve
    /// could call anything, so it is taken to reach `to`.
    fn reaches(&self, from: FuncId, to: FuncId) -> bool {
        let mut seen = BTreeSet::new();
        let mut stack = vec![from];
        while let Some(current) = stack.pop() {
            if current == to {
                return true;
            }
            if !seen.insert(current.index()) {
                continue;
            }
            let Some(function) = self.module.function_by_id(current) else {
                continue;
            };
            for block in &function.blocks {
                for node in &block.body {
                    match direct_callee(self.module, &node.inst) {
                        Some(DirectCallee::Named(callee)) => stack.push(callee),
                        Some(DirectCallee::UnresolvedDropGlue) => return true,
                        None => {}
                    }
                }
            }
        }
        false
    }

    fn define(&mut self, block_id: u32, target: TrustExpr, value: TrustExpr, what: &str) {
        let assumption = TrustExpr::implies(
            TrustExpr::variable(path_condition(block_id), TrustSort::Bool),
            TrustExpr::compare(TrustCompareOp::Eq, target, value),
        );
        self.assume(what, assumption);
    }

    fn assume(&mut self, what: &str, predicate: TrustExpr) {
        let id = format!("{}_{what}_{}", self.function.name, self.next_assumption);
        self.next_assumption += 1;
        self.relation.assumptions.push((id, predicate));
    }

    fn result_ref(
        &self,
        results: &[ValueId],
        block_id: u32,
    ) -> Result<(TrustExpr, TrustSort), Decline> {
        match results {
            [value] => self.value_ref(*value, block_id),
            other => Err(Decline::new(format!(
                "instruction in block {block_id} of `{}` produces {} results where one is \
                 required",
                self.function.name,
                other.len()
            ))),
        }
    }

    fn value_ref(&self, value: ValueId, block_id: u32) -> Result<(TrustExpr, TrustSort), Decline> {
        let entry = self.values.get(&value.index()).ok_or_else(|| {
            Decline::new(format!(
                "block {block_id} of `{}` uses value {} which no modelled instruction defines",
                self.function.name,
                value.index()
            ))
        })?;
        Ok((
            TrustExpr::variable(entry.emit.clone(), entry.sort.clone()),
            entry.sort.clone(),
        ))
    }

    fn bool_value(&self, value: ValueId, block_id: u32) -> Result<TrustExpr, Decline> {
        let (expr, sort) = self.value_ref(value, block_id)?;
        if sort != TrustSort::Bool {
            return Err(Decline::new(format!(
                "block {block_id} of `{}` branches on value {} of sort {}, which is not bool",
                self.function.name,
                value.index(),
                sort.display_label()
            )));
        }
        Ok(expr)
    }

    fn constant(
        &self,
        value: &Constant,
        sort: &TrustSort,
        block_id: u32,
    ) -> Result<TrustExpr, Decline> {
        match value {
            Constant::Bool(value) => {
                if *sort != TrustSort::Bool {
                    return Err(Decline::new(format!(
                        "boolean constant in block {block_id} of `{}` where {} is expected",
                        self.function.name,
                        sort.display_label()
                    )));
                }
                Ok(TrustExpr::bool_literal(*value))
            }
            Constant::Int(value) => match sort {
                TrustSort::BitVector { signed, width } => {
                    // SOUNDNESS (path-local contradiction): the literal must FIT
                    // the sort it is used at, in BOTH directions and at both
                    // signednesses. trust-ir's own reference semantics MASK an
                    // out-of-width integer to the declared width
                    // (`InterpretInt::from_i128`), so `256` at `u8` IS `0` and
                    // `200` at `i8` IS `-56` — while this lane would emit the
                    // literal as written, an equality no value of that sort can
                    // satisfy. Where the literal is a `Switch` case value that
                    // makes the arm's guard unsatisfiable and DROPS the arm the
                    // program actually takes; where it defines a value it makes
                    // that block's facts contradictory and erases the whole path.
                    // Either way the counterexample disappears and the obligation
                    // is "proved" over what survives. Modelling the mask instead
                    // would be new semantics on a hand-built bundle's word, so
                    // this fails closed. (`validate_module` types a `SwitchCase.value`
                    // against its selector too, so a bundle is refused upstream first;
                    // this gate covers a module lowered without that input gate.)
                    if !int_fits(*value, *signed, *width) {
                        return Err(Decline::new(format!(
                            "integer constant {value} in block {block_id} of `{}` does not fit \
                             the {} it is used at: trust-ir's interpreter MASKS an out-of-width \
                             constant to the declared width, so the literal as written is an \
                             equality no value of that sort satisfies — which would silently \
                             erase the path it guards rather than model the program",
                            self.function.name,
                            sort.display_label()
                        )));
                    }
                    Ok(TrustExpr::int_literal(*value, sort.clone()))
                }
                other => Err(Decline::new(format!(
                    "integer constant in block {block_id} of `{}` where {} is expected",
                    self.function.name,
                    other.display_label()
                ))),
            },
            // The uniform array constant `[elem; len]`. Its only legal type is
            // an array, which `TypeDecoder::sort` declines before any value is
            // lowered, so here it stands at a scalar sort. It declines by name,
            // rather than through the catch-all below, and neither `elem` nor
            // `len` is read, so the decline is the same at every length.
            Constant::Splat { .. } => Err(Decline::new(format!(
                "constant `Splat` in block {block_id} of `{}` is the uniform array \
                 `[elem; len]`, which inhabits no scalar sort ({} is expected): the discharge \
                 lane has no array sort",
                self.function.name,
                sort.display_label()
            ))),
            other => Err(Decline::new(format!(
                "constant `{}` in block {block_id} of `{}` is outside the scalar fragment",
                constant_name(other),
                self.function.name
            ))),
        }
    }
}

/// The single scalar sort a function returns, if any.
pub(crate) fn function_return_sort(
    module: &Module,
    function: &Function,
    types: TypeDecoder,
) -> Result<Option<TrustSort>, Decline> {
    let func_ty = usize::try_from(function.ty.index())
        .ok()
        .and_then(|index| module.func_types.get(index))
        .ok_or_else(|| {
            Decline::new(format!(
                "function `{}` references func type {} which is not in the module",
                function.name,
                function.ty.index()
            ))
        })?;
    match func_ty.returns.as_slice() {
        [] => Ok(None),
        [ty] => Ok(Some(types.sort(ty).map_err(|decline| {
            Decline::new(format!(
                "return type of `{}`: {}",
                function.name,
                decline.reason()
            ))
        })?)),
        many => Err(Decline::new(format!(
            "function `{}` returns {} values; the discharge lane models a single scalar return \
             (or none)",
            function.name,
            many.len()
        ))),
    }
}

/// Arguments an edge from `source` carries to `target`.
///
/// The type an instruction's single result carries, when this lane models it at
/// all. `None` means the instruction produces no value.
fn result_ty(inst: &Inst, module: &Module) -> Option<Result<Ty, Decline>> {
    match inst {
        Inst::Const { ty, .. }
        | Inst::Copy { ty, .. }
        | Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Select { ty, .. } => Some(Ok(ty.clone())),
        // An `ICmp`'s `ty` is the OPERAND type; the result is always `bool`.
        Inst::ICmp { .. } => Some(Ok(Ty::Bool)),
        Inst::Cast { dst_ty, .. } => Some(Ok(dst_ty.clone())),
        Inst::Call { callee, .. } => module.function_by_id(*callee).and_then(|callee| {
            usize::try_from(callee.ty.index())
                .ok()
                .and_then(|index| module.func_types.get(index))
                .and_then(|func_ty| func_ty.returns.first().cloned())
                .map(Ok)
        }),
        // The uniform array `[v; n]` has an array result, which no sort here
        // models. Its result is never declared, and `lower_inst` declines the
        // instruction by name.
        Inst::ArraySplat { .. } => None,
        // No closure value is declared: lower_inst refuses the constructor
        // even if its result is unused.
        Inst::MakeClosure { .. } => None,
        _ => None,
    }
}

fn binary(
    op: BinOp,
    sort: &TrustSort,
    left: (TrustExpr, TrustSort),
    right: (TrustExpr, TrustSort),
    block_id: u32,
    index: usize,
) -> Result<TrustExpr, Decline> {
    if left.1 != right.1 {
        return Err(Decline::new(format!(
            "block {block_id} instruction {index}: operands are {} and {}",
            left.1.display_label(),
            right.1.display_label()
        )));
    }
    let arith = |op| TrustExpr::arith(op, left.0.clone(), right.0.clone(), sort.clone());
    match op {
        BinOp::Add => Ok(arith(TrustArithOp::Add)),
        BinOp::Sub => Ok(arith(TrustArithOp::Sub)),
        BinOp::Mul => Ok(arith(TrustArithOp::Mul)),
        // The division operators name their signedness; trust-vc carries it on
        // the sort, so a mismatch is not expressible without changing meaning.
        BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem => {
            let signed = matches!(op, BinOp::SDiv | BinOp::SRem);
            match sort {
                TrustSort::BitVector { signed: actual, .. } if *actual == signed => {
                    Ok(arith(if matches!(op, BinOp::UDiv | BinOp::SDiv) {
                        TrustArithOp::Div
                    } else {
                        TrustArithOp::Rem
                    }))
                }
                other => Err(Decline::new(format!(
                    "block {block_id} instruction {index}: `{op:?}` is a {} operation over {} \
                     operands",
                    if signed { "signed" } else { "unsigned" },
                    other.display_label()
                ))),
            }
        }
        // The UNAMBIGUOUS boolean connectives. `And`/`Or`/`Xor` are deliberately
        // NOT accepted: trust-ir documents them as bitwise-for-integers and
        // logical-for-bools, an overloading whose bool reading denotes through an
        // opaque integer carrier — exactly the gap `BAnd`/`BOr`/`BXor` exist to
        // close. A frontend that means the connective says so.
        BinOp::BAnd | BinOp::BOr => {
            if *sort != TrustSort::Bool {
                return Err(Decline::new(format!(
                    "block {block_id} instruction {index}: `{op:?}` over {} operands",
                    sort.display_label()
                )));
            }
            Ok(TrustExpr::logic(
                if matches!(op, BinOp::BAnd) {
                    TrustLogicOp::And
                } else {
                    TrustLogicOp::Or
                },
                left.0,
                right.0,
            ))
        }
        BinOp::BXor => {
            if *sort != TrustSort::Bool {
                return Err(Decline::new(format!(
                    "block {block_id} instruction {index}: `BXor` over {} operands",
                    sort.display_label()
                )));
            }
            Ok(TrustExpr::not(TrustExpr::compare(
                TrustCompareOp::Eq,
                left.0,
                right.0,
            )))
        }
        other => Err(Decline::new(format!(
            "block {block_id} instruction {index}: `BinOp::{other:?}` is outside the scalar \
             fragment"
        ))),
    }
}

fn unary(
    op: UnOp,
    sort: &TrustSort,
    operand: (TrustExpr, TrustSort),
    block_id: u32,
    index: usize,
) -> Result<TrustExpr, Decline> {
    match op {
        UnOp::Not if *sort == TrustSort::Bool && operand.1 == TrustSort::Bool => {
            Ok(TrustExpr::not(operand.0))
        }
        other => Err(Decline::new(format!(
            "block {block_id} instruction {index}: `UnOp::{other:?}` over {} is outside the \
             scalar fragment (integer `Not` is bitwise and `Neg` is a checked negation, neither \
             of which the boundary expression carries)",
            operand.1.display_label()
        ))),
    }
}

fn compare(
    op: ICmpOp,
    left: (TrustExpr, TrustSort),
    right: (TrustExpr, TrustSort),
    block_id: u32,
    index: usize,
) -> Result<TrustExpr, Decline> {
    if left.1 != right.1 {
        return Err(Decline::new(format!(
            "block {block_id} instruction {index}: comparison operands are {} and {}",
            left.1.display_label(),
            right.1.display_label()
        )));
    }
    let signed = match op {
        ICmpOp::Eq | ICmpOp::Ne => None,
        ICmpOp::Ult | ICmpOp::Ule | ICmpOp::Ugt | ICmpOp::Uge => Some(false),
        ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge => Some(true),
    };
    if let Some(signed) = signed {
        match &left.1 {
            TrustSort::BitVector { signed: actual, .. } if *actual == signed => {}
            other => {
                return Err(Decline::new(format!(
                    "block {block_id} instruction {index}: `{op:?}` is a {} comparison over {} \
                     operands; trust-vc carries signedness on the sort, so this cannot be \
                     expressed without changing what is asserted",
                    if signed { "signed" } else { "unsigned" },
                    other.display_label()
                )))
            }
        }
    }
    let compare_op = match op {
        ICmpOp::Eq => TrustCompareOp::Eq,
        ICmpOp::Ne => TrustCompareOp::Ne,
        ICmpOp::Ult | ICmpOp::Slt => TrustCompareOp::Lt,
        ICmpOp::Ule | ICmpOp::Sle => TrustCompareOp::Le,
        ICmpOp::Ugt | ICmpOp::Sgt => TrustCompareOp::Gt,
        ICmpOp::Uge | ICmpOp::Sge => TrustCompareOp::Ge,
    };
    Ok(TrustExpr::compare(compare_op, left.0, right.0))
}

fn cast(
    op: CastOp,
    src: TrustSort,
    dst: TrustSort,
    operand: (TrustExpr, TrustSort),
    result: &TrustSort,
    block_id: u32,
    index: usize,
) -> Result<TrustExpr, Decline> {
    if operand.1 != src || *result != dst {
        return Err(Decline::new(format!(
            "block {block_id} instruction {index}: cast declares {} -> {} but its operand is {} \
             and its result is {}",
            src.display_label(),
            dst.display_label(),
            operand.1.display_label(),
            result.display_label()
        )));
    }
    // MEASURED: `TrustExpr::Cast` carries only the two sorts. The encoder picks
    // the extension from the SOURCE sort's signedness and picks extend-vs-narrow
    // by comparing the two WIDTHS — the `CastOp` is not on the wire at all. So
    // the op has to agree with the sorts, or the expression denotes a different
    // function than the instruction does. trust-ir's own interpreter settles
    // which reading is authoritative: `CastOp::SExt` evaluates
    // `InterpretInt::as_signed()`, which reads the raw bits in two's complement
    // and IGNORES the source type's own signedness, so `200u8 as i32` is `-56`
    // while the sort-derived reading gives `200`.
    let source_extension = match &src {
        TrustSort::BitVector { signed, .. } => *signed,
        // Bool -> integer is `false = 0, true = 1`, which is the ZERO
        // extension; `SExt` from `Bool` would set every destination bit
        // (`true -> -1`), which is not what a `bool as iN` cast means.
        TrustSort::Bool => false,
        other => {
            return Err(Decline::new(format!(
                "block {block_id} instruction {index}: `CastOp::{op:?}` from {} is outside the \
                 scalar fragment",
                other.display_label()
            )))
        }
    };
    let widths = |sort: &TrustSort| match sort {
        TrustSort::BitVector { width, .. } => Some(*width),
        _ => None,
    };
    match op {
        // Truncation keeps the low bits whichever way the operand is read, so
        // it is signedness-agnostic — but it must actually NARROW, or the
        // encoder's width comparison turns it into an extension.
        CastOp::Trunc => match (widths(&src), widths(&dst)) {
            (Some(source), Some(destination)) if source > destination => {
                Ok(TrustExpr::cast(operand.0, src, dst))
            }
            _ => Err(Decline::new(format!(
                "block {block_id} instruction {index}: `CastOp::Trunc` from {} to {} does not \
                 narrow between two fixed widths, and the boundary expression chooses \
                 narrow-vs-extend by comparing widths, so it would be encoded as an EXTENSION",
                src.display_label(),
                dst.display_label()
            ))),
        },
        CastOp::ZExt | CastOp::SExt => {
            let wants_signed = matches!(op, CastOp::SExt);
            if source_extension != wants_signed {
                return Err(Decline::new(format!(
                    "block {block_id} instruction {index}: `CastOp::{op:?}` from {} to {} would \
                     be encoded as a {} extension, because trust-vc carries signedness on the \
                     SORT and this operand's sort is {}; trust-ir reads the operand's raw bits \
                     in two's complement for `SExt` whatever the source type says, so modelling \
                     it here would assert something the IR does not mean",
                    src.display_label(),
                    dst.display_label(),
                    if source_extension { "sign" } else { "zero" },
                    src.display_label()
                )));
            }
            match (widths(&src), widths(&dst)) {
                // A `Bool` source has no width; `bool -> iN` is the 0/1 term,
                // which is an extension in every direction that type-checks.
                (None, Some(_)) if src == TrustSort::Bool => {
                    Ok(TrustExpr::cast(operand.0, src, dst))
                }
                (Some(source), Some(destination)) if source < destination => {
                    Ok(TrustExpr::cast(operand.0, src, dst))
                }
                _ => Err(Decline::new(format!(
                    "block {block_id} instruction {index}: `CastOp::{op:?}` from {} to {} does \
                     not widen between two fixed widths, and the boundary expression chooses \
                     narrow-vs-extend by comparing widths, so it would be encoded as a \
                     TRUNCATION",
                    src.display_label(),
                    dst.display_label()
                ))),
            }
        }
        other => Err(Decline::new(format!(
            "block {block_id} instruction {index}: `CastOp::{other:?}` from {} to {} is outside \
             the scalar fragment",
            src.display_label(),
            dst.display_label()
        ))),
    }
}

/// The namespace the per-block path-condition variables live in.
///
/// SOUNDNESS: these share ONE flat namespace with the producer's value names,
/// so the prefix has to be RESERVED rather than merely unlikely. `$` is not a
/// Rust identifier character, but a hand-built or replayed bundle is not Rust
/// source and nothing between the producer and this lane checks.
const PATH_CONDITION_PREFIX: &str = "pc$";

fn path_condition(block_id: u32) -> String {
    format!("{PATH_CONDITION_PREFIX}{block_id}")
}

/// What a producer-supplied name would collide with, if anything.
///
/// The unit declares ONE variable per name. A producer value spelled `_0` and
/// the return place are therefore the same variable, and `pc$b => _0 == …`
/// pins the producer's value to the returned one — false in the program. A
/// value spelled `pc$0` IS block 0's path condition, and `pc$0 == true` forces
/// the producer's value true. Both are refused by name rather than renamed:
/// renaming would silently change what a contract clause spelling that name
/// resolves to.
fn reserved_name(name: &str) -> Option<&'static str> {
    if name == RESULT_VAR {
        Some("the return place")
    } else if name.starts_with(PATH_CONDITION_PREFIX) {
        Some("the per-block path-condition namespace")
    } else {
        None
    }
}

/// A name for an instruction, so a decline says what it refused.
fn inst_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::PtrData { .. } => "PtrData",
        Inst::PtrMetadata { .. } => "PtrMetadata",
        Inst::PtrFromParts { .. } => "PtrFromParts",
        Inst::AtomicLoad { .. } => "AtomicLoad",
        Inst::AtomicStore { .. } => "AtomicStore",
        Inst::AtomicRMW { .. } => "AtomicRMW",
        Inst::CmpXchg { .. } => "CmpXchg",
        Inst::Drop { .. } => "Drop",
        Inst::Fence { .. } => "Fence",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::Const { .. } => "Const",
        Inst::NullPtr => "NullPtr",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        Inst::SeqMapAddK { .. } => "SeqMapAddK",
        Inst::SeqMapNot { .. } => "SeqMapNot",
        Inst::SeqMap { .. } => "SeqMap",
        Inst::Borrow { .. } => "Borrow",
        Inst::BorrowMut { .. } => "BorrowMut",
        Inst::EndBorrow { .. } => "EndBorrow",
        Inst::Retain { .. } => "Retain",
        Inst::Release { .. } => "Release",
        Inst::IsUnique { .. } => "IsUnique",
        Inst::Dealloc { .. } => "Dealloc",
        // trust-ir v50's uniform array `[v; n]`. The name does not read `n`.
        Inst::ArraySplat { .. } => "ArraySplat",
        Inst::MakeClosure { .. } => "MakeClosure",
        Inst::AssertInvoke { .. } => "AssertInvoke",
        Inst::CallCannotUnwind { .. } => "CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
        Inst::DropInvoke { .. } => "DropInvoke",
        Inst::InvokeIndirect { .. } => "InvokeIndirect",
        // The tensor region (trust-ir v67-v69). The lane has no tensor sort,
        // so `lower_inst`'s catch-all declines each one under this name.
        Inst::TensorContract { .. } => "TensorContract",
        Inst::TensorMap { .. } => "TensorMap",
        Inst::TensorReduce { .. } => "TensorReduce",
        Inst::TensorView { .. } => "TensorView",
        Inst::TensorGather { .. } => "TensorGather",
        Inst::TensorScatter { .. } => "TensorScatter",
        #[allow(unreachable_patterns)]
        _ => "unknown",
    }
}

/// Does `value` fit a `width`-bit integer of that signedness?
///
/// The bound is the DECLARED type's, not the encoder's convenience: a literal
/// outside it denotes a different value under trust-ir's masking interpreter, so
/// the caller declines rather than emitting it. `u128`/`i128` need the widened
/// comparison — `1i128 << 127` overflows — so the top widths are answered
/// without forming the bound.
fn int_fits(value: i128, signed: bool, width: u32) -> bool {
    if width == 0 || width > 128 {
        // Not a width this lane can bound. Nothing fits it.
        return false;
    }
    if signed {
        if width == 128 {
            return true;
        }
        let bound = 1i128 << (width - 1);
        value >= -bound && value < bound
    } else {
        if value < 0 {
            return false;
        }
        if width >= 127 {
            // Every non-negative `i128` is below `2^127`, hence below `2^width`.
            return true;
        }
        value < (1i128 << width)
    }
}

fn constant_name(value: &Constant) -> &'static str {
    match value {
        Constant::Int(_) => "Int",
        Constant::U128(_) => "U128",
        Constant::Bytes { .. } => "Bytes",
        Constant::Float(_) => "Float",
        Constant::Bool(_) => "Bool",
        Constant::Aggregate(_) => "Aggregate",
        Constant::Array(_) => "Array",
        // trust-ir v50's uniform array constant `[elem; len]`. The name does
        // not read `len`.
        Constant::Splat { .. } => "Splat",
        Constant::Vector(_) => "Vector",
        Constant::Sequence(_) => "Sequence",
        Constant::Set(_) => "Set",
        Constant::Record(_) => "Record",
        Constant::FnDef(_) => "FnDef",
        Constant::PhantomData => "PhantomData",
        Constant::Uninit => "Uninit",
        // trust-ir v70's weight constant. The name reads neither the digest
        // nor the extents.
        Constant::TensorBlob { .. } => "TensorBlob",
        #[allow(unreachable_patterns)]
        _ => "unknown",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::inst::SwitchCase;
    use trust_ir::node::InstrNode;
    use trust_ir::{
        BlockId, Endianness, FuncTy, FuncTyId, ObligationSite, ProofId, StructPassingPolicy,
        TargetInfo,
    };

    fn v(id: u32) -> ValueId {
        ValueId::new(id)
    }

    fn b(id: u32) -> BlockId {
        BlockId::new(id)
    }

    fn module_with(function: Function, func_ty: FuncTy) -> Module {
        let mut module = Module::new("probe");
        module.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
        module.func_types.push(func_ty);
        module.functions.push(function);
        module
    }

    /// `fn inc(x: u64) -> u64 { x + 1 }`, one block.
    fn inc_function(tail: Vec<InstrNode>) -> (Module, FuncId) {
        let mut function = Function::new(FuncId::new(0), "inc", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::U64));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            })
            .with_result(v(1)),
        );
        entry.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        entry.body.extend(tail);
        function.blocks.push(entry);
        function.value_names = Some(vec![(v(0), "x".to_string())]);
        (
            module_with(
                function,
                FuncTy {
                    params: vec![Ty::U64],
                    returns: vec![Ty::U64],
                    is_vararg: false,
                    abi: None,
                },
            ),
            FuncId::new(0),
        )
    }

    fn lower(module: &Module) -> Result<BodyRelation, Decline> {
        let types = TypeDecoder::from_module(module);
        lower_body(module, &module.functions[0], FuncId::new(0), types)
    }

    #[test]
    fn lowers_a_straight_line_scalar_body() {
        let (module, _) = inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        let relation = lower(&module).expect("the scalar fragment lowers");

        // The parameter is named from `value_names`; the return place is `_0`,
        // which is what a producer-emitted `ensures` spells.
        assert_eq!(relation.variables.get("x"), Some(&TrustSort::unsigned(64)));
        assert_eq!(
            relation.variables.get(RESULT_VAR),
            Some(&TrustSort::unsigned(64))
        );
        assert_eq!(relation.variables.get("pc$0"), Some(&TrustSort::Bool));
        assert!(relation.scope.contains_key("x"));
        assert!(relation.scope.contains_key(RESULT_VAR));
        // Entry path condition, the two definitions, and the return binding.
        assert_eq!(relation.assumptions.len(), 4);
        // The `+` is decided at the declared machine width, and its
        // arithmetic-safety is a separate panic-freedom obligation — recorded
        // rather than silently inherited.
        assert_eq!(relation.premises.len(), 1);
        assert_eq!(
            relation.premises[0].kind(),
            TrustVcNativeTrustIrPremiseKind::MachineArithmetic
        );
    }

    #[test]
    fn unused_runtime_closure_declines_before_relational_lowering() {
        let (mut module, _) =
            inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        let apparent = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        let physical = module
            .add_func_type(FuncTy {
                params: vec![Ty::U64; 3],
                returns: vec![],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        let closure = module
            .add_closure_type(trust_ir::ClosureTy {
                func: apparent,
                captures: vec![Ty::U64; 3],
            })
            .unwrap();
        let mut target = Function::new(FuncId::new(1), "target", physical, b(0));
        let mut block = Block::new(b(0));
        block.params = (0..3).map(|index| (v(index), Ty::U64)).collect();
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        target.blocks.push(block);
        module.try_add_function(target).unwrap();
        module.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::MakeClosure {
                ty: closure,
                func: FuncId::new(1),
                captures: vec![v(0); 3],
            })
            .with_result(v(99)),
        );
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let refusal = lower(&module).expect_err("an unused constructor must not disappear");
        assert!(refusal.reason().contains("instruction 0"), "{refusal}");
        assert!(refusal.reason().contains("MakeClosure"), "{refusal}");
        assert!(
            refusal.reason().contains("ordered live captures"),
            "{refusal}"
        );
        module.functions[0].blocks[0].body.remove(0);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        lower(&module).expect("the scalar twin remains in the supported fragment");
    }

    /// Two branches joining at a block parameter — the phi case, encoded as
    /// per-edge guarded equalities rather than a conditional term.
    #[test]
    fn lowers_a_two_branch_join_through_block_parameters() {
        let mut function = Function::new(FuncId::new(0), "pick", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::Bool));
        entry.params.push((v(1), Ty::I32));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![v(1)],
            else_target: b(2),
            else_args: vec![v(2)],
        }));
        let mut then_block = Block::new(b(1));
        then_block.params.push((v(3), Ty::I32));
        then_block.body.push(InstrNode::new(Inst::Br {
            target: b(3),
            args: vec![v(3)],
        }));
        let mut else_block = Block::new(b(2));
        else_block.params.push((v(4), Ty::I32));
        else_block.body.push(InstrNode::new(Inst::Br {
            target: b(3),
            args: vec![v(4)],
        }));
        let mut join = Block::new(b(3));
        join.params.push((v(5), Ty::I32));
        join.body
            .push(InstrNode::new(Inst::Return { values: vec![v(5)] }));
        function
            .blocks
            .extend([entry, then_block, else_block, join]);

        let module = module_with(
            function,
            FuncTy {
                params: vec![Ty::Bool, Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: None,
            },
        );
        let relation = lower(&module).expect("an acyclic two-branch body lowers");
        for block in 0..4 {
            assert!(relation.variables.contains_key(&format!("pc${block}")));
        }
        // Every block parameter is bound once per incoming edge: one for each
        // arm's own parameter, and two for the join's.
        assert_eq!(
            relation
                .assumptions
                .iter()
                .filter(|(id, _)| id.contains("phi"))
                .count(),
            4
        );
    }

    /// A back edge is a LOOP, and the pinned schema carries no invariant anchor.
    /// Unrolling it would be a bounded check reported as a proof.
    #[test]
    fn a_back_edge_declines_naming_the_loop() {
        let mut function = Function::new(FuncId::new(0), "spin", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::Bool));
        entry.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        }));
        let mut loop_block = Block::new(b(1));
        loop_block.body.push(InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        }));
        let mut exit = Block::new(b(2));
        exit.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.extend([entry, loop_block, exit]);
        let module = module_with(
            function,
            FuncTy {
                params: vec![Ty::Bool],
                returns: vec![],
                is_vararg: false,
                abi: None,
            },
        );
        let decline = lower(&module).expect_err("a loop is not in the acyclic fragment");
        assert!(decline.reason().contains("back edge"), "{decline}");
        assert!(decline.reason().contains("block 1"), "{decline}");
    }

    /// THE FAIL-CLOSED SURFACE of the body lane. Each of these is a construct
    /// that, modelled wrongly, would be a false `Verified`.
    #[test]
    fn every_unmodelled_instruction_declines_naming_itself() {
        let cases: Vec<(Inst, &str)> = vec![
            // Claiming a path cannot happen is `assume(false)` on it, under
            // which every obligation is provable.
            (Inst::Unreachable, "Unreachable"),
            // Memory: promoting allocas first would renumber the `(block,
            // inst_index)` anchors every obligation binds to.
            (
                Inst::Alloca {
                    ty: Ty::U64,
                    count: None,
                    align: None,
                },
                "Alloca",
            ),
            (
                Inst::Load {
                    ty: Ty::U64,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
                "Load",
            ),
            (
                Inst::Store {
                    ty: Ty::U64,
                    ptr: v(0),
                    value: v(2),
                    volatile: false,
                    align: None,
                },
                "Store",
            ),
            // A check the program makes is a proof obligation, not a fact.
            (
                Inst::Assert {
                    cond: v(0),
                    kind: Default::default(),
                    site: None,
                },
                "Assert",
            ),
            // Checked arithmetic carries an overflow side-channel the boundary
            // expression does not model.
            (
                Inst::Overflow {
                    op: trust_ir::inst::OverflowOp::AddOverflow,
                    ty: Ty::U64,
                    lhs: v(0),
                    rhs: v(1),
                },
                "Overflow",
            ),
            (
                Inst::CallIndirect {
                    callee: v(0),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                },
                "CallIndirect",
            ),
            (Inst::Undef { ty: Ty::U64 }, "Undef"),
            (Inst::Borrow { ptr: v(0) }, "Borrow"),
            (Inst::BorrowMut { ptr: v(0) }, "BorrowMut"),
            (Inst::EndBorrow { borrow_ptr: v(0) }, "EndBorrow"),
            (
                Inst::ExtractField {
                    ty: Ty::U64,
                    aggregate: v(0),
                    field: 0,
                },
                "ExtractField",
            ),
            (
                Inst::GEP {
                    pointee_ty: Ty::U64,
                    base: v(0),
                    indices: vec![],
                    inbounds: true,
                },
                "GEP",
            ),
        ];
        for (inst, name) in cases {
            let (module, _) = inc_function(vec![
                InstrNode::new(inst).with_result(v(9)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ]);
            let decline = lower(&module).expect_err("instruction is outside the fragment");
            assert!(
                decline.reason().contains(name),
                "decline for {name} must name it, got: {decline}"
            );
        }
    }

    /// trust-ir v50's constant-size uniform array `[v; n]` declines BY NAME in
    /// every spelling: the register `ArraySplat` at the instruction, a `Const`
    /// at its array type at the type, and a `Splat` at a scalar type at the
    /// constant.
    ///
    /// The decline must cost the same at every length. Nothing here times
    /// anything: the SAME decline comes back at two copies and at `u64::MAX`
    /// copies, and a pass that walked `n` could not return at 2^64 elements.
    /// The test itself allocates nothing per element.
    #[test]
    fn a_uniform_array_declines_naming_itself_at_every_length() {
        let declines = |len: u64| {
            [0, 1, 2].map(|spelling| {
                let (mut module, _) = inc_function(Vec::new());
                let elem = module
                    .add_type(Ty::U64)
                    .expect("Module::add_type: test fixture");
                let array = Ty::Array(elem, len);
                let splat = Constant::splat(Constant::Int(1), len);
                let inst = match spelling {
                    0 => Inst::ArraySplat {
                        ty: array,
                        value: v(0),
                    },
                    1 => Inst::Const {
                        ty: array,
                        value: splat,
                    },
                    _ => Inst::Const {
                        ty: Ty::U64,
                        value: splat,
                    },
                };
                module.functions[0].blocks[0].body.extend([
                    InstrNode::new(inst).with_result(v(9)),
                    InstrNode::new(Inst::Return { values: vec![v(2)] }),
                ]);
                lower(&module)
                    .expect_err("a uniform array is outside the fragment")
                    .into_reason()
            })
        };
        let small = declines(2);
        // The register and scalar-constant spellings decline in their own
        // arms, not through the catch-alls, whose messages lack these words.
        assert!(
            small[0].contains("is `ArraySplat`, the uniform array `[v; n]`"),
            "{}",
            small[0]
        );
        assert!(
            small[1].contains("unmodelled trust-ir type `Array`"),
            "{}",
            small[1]
        );
        assert!(
            small[2].contains("constant `Splat`")
                && small[2].contains("inhabits no scalar sort (u64 is expected)"),
            "{}",
            small[2]
        );
        for len in [2, 1 << 40, u64::MAX] {
            // No decline mentions the length, so each is the SAME decline at
            // every length.
            assert_eq!(declines(len), small, "len {len}");
        }
    }

    /// The six tensor operations of trust-ir v67-v69, each spelled in
    /// trust-ir's own text grammar and parsed by trust-ir's own parser, so no
    /// fixture field is a guess about the producer's shape. Every operand id
    /// is 10 or above, so none is defined in the host body a test splices an
    /// operation into.
    fn tensor_operations() -> Vec<(&'static str, Inst)> {
        let text = "; TrustIr text format v1
module \"tensor_operations\"

functy.0 = (tensor<i32, 2>, tensor<i32, 2>, i32, usize) -> ()

fn @t(functy.0) {
bb0(%10: tensor<i32, 2>, %11: tensor<i32, 2>, %12: i32, %13: usize):
    %14 = tensor_contract tensor<i32, 2> %10, %11 batch [] contract [1:0]
    %15 = tensor_map tensor<i32, 2> (%10, %11, %12) { add i32 $0, $1; neg i32 $3 }
    %16 = tensor_reduce smax tensor<i32, 1> %10 axes [0] order row_major
    %17 = tensor_view tensor<i32, 2> %10 params [%13] exprs [coord(1), coord(0)] shape [$0, $1] index [$1, $0] fill %12
    %18 = tensor_gather tensor<i32, 1> %10 coords [%12, %13]
    %19 = tensor_scatter tensor<i32, 2> %10, %11 coords [%12, %13]
    ret
}
";
        let module = trust_ir::parser::parse_module(text).expect("trust-ir parses its own text");
        let names = [
            "TensorContract",
            "TensorMap",
            "TensorReduce",
            "TensorView",
            "TensorGather",
            "TensorScatter",
        ];
        let body = &module.functions[0].blocks[0].body;
        assert_eq!(body.len(), names.len() + 1, "six operations and a return");
        names
            .into_iter()
            .zip(body.iter().map(|node| node.inst.clone()))
            .collect()
    }

    /// `inc` with `node` spliced in after its scalar body, before its return.
    fn inc_with(node: InstrNode) -> Module {
        let (mut module, _) = inc_function(Vec::new());
        module.functions[0].blocks[0]
            .body
            .extend([node, InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        module
    }

    /// trust-ir v67-v69's tensor operations decline BY NAME in the lowering,
    /// before any operand is read: no operand here is defined in the host body
    /// (which defines v0..v2 and the spliced result v9), and the decline is
    /// still the named one.
    #[test]
    fn every_tensor_operation_declines_naming_itself() {
        let operations = tensor_operations();
        assert_eq!(operations.len(), 6);
        for (name, inst) in operations {
            assert_eq!(inst_name(&inst), name);
            let decline = lower(&inc_with(InstrNode::new(inst).with_result(v(9))))
                .expect_err("a tensor operation is outside the fragment")
                .into_reason();
            assert!(
                decline.contains(&format!(
                    "is `{name}`, which the discharge lane does not model"
                )),
                "{name}: {decline}"
            );
        }
    }

    /// A `Ty::Tensor` (trust-ir v67) declines through `TypeDecoder::sort`,
    /// naming the type, at an entry parameter (`declare_values`) and at the
    /// return (`function_return_sort`). The twin is the scalar `inc`.
    #[test]
    fn a_tensor_type_declines_at_a_parameter_and_a_return() {
        let tensor = || Ty::Tensor(Box::new(Ty::I32), 2);
        let (twin, _) = inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        lower(&twin).expect("the scalar twin lowers");
        let mut at_parameter = twin.clone();
        at_parameter.func_types[0].params.push(tensor());
        at_parameter.functions[0].blocks[0]
            .params
            .push((v(8), tensor()));
        let mut at_return = twin.clone();
        at_return.func_types[0].returns = vec![tensor()];
        for (site, module, expected) in [
            (
                "parameter",
                at_parameter,
                "unmodelled trust-ir type `Tensor`",
            ),
            (
                "return",
                at_return,
                "return type of `inc`: unmodelled trust-ir type `Tensor`",
            ),
        ] {
            let decline = lower(&module)
                .expect_err("a tensor type is outside the fragment")
                .into_reason();
            assert!(decline.contains(expected), "{site}: {decline}");
        }
    }

    /// trust-ir v70's weight constant declines BY NAME: at its tensor type the
    /// type declines first, and at a scalar sort the constant lowering names
    /// it. The twin, an integer at the same scalar sort, lowers.
    #[test]
    fn a_tensor_blob_constant_declines_naming_itself() {
        let digest = Module::new("scratch").intern_blob(vec![0; 8]);
        let constant = |ty: Ty, value: Constant| {
            lower(&inc_with(
                InstrNode::new(Inst::Const { ty, value }).with_result(v(9)),
            ))
        };
        let blob = || Constant::TensorBlob {
            digest,
            dims: vec![2],
        };
        let at_tensor = constant(Ty::Tensor(Box::new(Ty::I32), 1), blob())
            .expect_err("a tensor type is outside the fragment")
            .into_reason();
        assert!(
            at_tensor.contains("unmodelled trust-ir type `Tensor`"),
            "{at_tensor}"
        );
        let at_scalar = constant(Ty::U64, blob())
            .expect_err("a tensor blob inhabits no scalar sort")
            .into_reason();
        assert!(
            at_scalar.contains("constant `TensorBlob`")
                && at_scalar.contains("outside the scalar fragment"),
            "{at_scalar}"
        );
        constant(Ty::U64, Constant::Int(7)).expect("the integer twin lowers");
    }

    /// A module carrying a weight blob table (`Module.blobs`, trust-ir v70)
    /// declines whole, by the table's name, even when the lowered body is in
    /// the fragment and cites no row. The twin differs by the one blob.
    #[test]
    fn a_module_carrying_blobs_declines_naming_the_table() {
        let (twin, _) = inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        lower(&twin).expect("the scalar fragment lowers");
        let mut carrying = twin.clone();
        carrying.intern_blob(vec![1, 2, 3, 4]);
        let decline = lower(&carrying)
            .expect_err("a module carrying blobs is outside the lane")
            .into_reason();
        assert!(
            decline.contains("1 weight blob row(s) (`Module.blobs`)"),
            "{decline}"
        );
    }

    /// Two SSA values carrying the same source name make every clause naming it
    /// ambiguous — the shadowing gate, enforced rather than assumed.
    #[test]
    fn duplicate_source_names_decline() {
        let (mut module, _) =
            inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        module.functions[0].value_names =
            Some(vec![(v(0), "x".to_string()), (v(2), "x".to_string())]);
        let decline = lower(&module).expect_err("shadowed names are ambiguous");
        assert!(decline.reason().contains("ambiguous"), "{decline}");
    }

    /// A signed operator over an unsigned-declared operand is not expressible on
    /// a boundary expression that carries signedness on the SORT, so it declines
    /// rather than silently becoming the other operation.
    #[test]
    fn signedness_mismatches_decline() {
        let (module, _) = {
            let (mut module, id) =
                inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
            module.functions[0].blocks[0].body[1] = InstrNode::new(Inst::BinOp {
                op: BinOp::SDiv,
                ty: Ty::U64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2));
            (module, id)
        };
        let decline = lower(&module).expect_err("SDiv over u64");
        assert!(decline.reason().contains("signed"), "{decline}");
    }

    /// Assuming a recursive callee's `ensures` to prove that same `ensures` is
    /// only sound with a termination measure, and the pinned schema has none.
    #[test]
    fn a_recursive_call_declines() {
        let (mut module, _) = inc_function(vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![v(0)],
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Return { values: vec![v(3)] }),
        ]);
        module.functions[0].value_names = Some(vec![(v(0), "x".to_string())]);
        let decline = lower(&module).expect_err("self-recursion has no termination measure");
        assert!(decline.reason().contains("recursion cycle"), "{decline}");
    }

    /// A `Switch` lowers to per-case equality guards and a default that is the
    /// conjunction of the disequalities.
    #[test]
    fn a_switch_lowers_to_guarded_edges() {
        let mut function = Function::new(FuncId::new(0), "pick", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::I32));
        entry.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(2),
            default_args: vec![],
            cases: vec![SwitchCase {
                value: Constant::Int(7),
                target: b(1),
                args: vec![],
            }],
            exhaustive_enum_unreachable: false,
        }));
        let mut case = Block::new(b(1));
        case.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut default = Block::new(b(2));
        default
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.extend([entry, case, default]);
        let module = module_with(
            function,
            FuncTy {
                params: vec![Ty::I32],
                returns: vec![],
                is_vararg: false,
                abi: None,
            },
        );
        let relation = lower(&module).expect("an integer switch lowers");
        assert!(relation.variables.contains_key("pc$1"));
        assert!(relation.variables.contains_key("pc$2"));
    }

    /// A `Switch` on `x` with the given case values, returning a `u32`.
    ///
    /// The arms DISAGREE (one returns 0, one returns 5), which is what turns a
    /// pair of simultaneously-live guards into a contradictory path rather than
    /// a harmless duplicate.
    fn switch_case_module(case_values: Vec<Constant>) -> Module {
        let mut function = Function::new(FuncId::new(0), "f", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::U32));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(5),
            })
            .with_result(v(2)),
        );
        entry.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(3),
            default_args: vec![],
            cases: case_values
                .into_iter()
                .enumerate()
                .map(|(index, value)| SwitchCase {
                    value,
                    target: b(u32::try_from(index).expect("two cases") + 1),
                    args: vec![],
                })
                .collect(),
            exhaustive_enum_unreachable: false,
        }));
        let mut first = Block::new(b(1));
        first
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        let mut second = Block::new(b(2));
        second
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        let mut default = Block::new(b(3));
        default
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        function.blocks.extend([entry, first, second, default]);
        function.value_names = Some(vec![(v(0), "x".to_string())]);
        module_with(
            function,
            FuncTy {
                params: vec![Ty::U32],
                returns: vec![Ty::U32],
                is_vararg: false,
                abi: None,
            },
        )
    }

    /// REGRESSION, adversarial review round 3 (F1): two `Switch` cases carrying
    /// the SAME value are a PATH-LOCAL CONTRADICTION, not a harmless duplicate.
    ///
    /// Both guards are `x == c`, so both arms are live at once and their facts
    /// collide (`_0 == 0` and `_0 == 5`); that path then has no model, the
    /// solver never explores it, and the counterexample living on it is ERASED.
    /// The engine's `VacuousTruth` detector does not fire, because the rest of
    /// the assumption set is perfectly satisfiable. Probed as
    /// `fn f(x: u32) -> u32 { switch x { 0 => 0, 0 => 1, _ => 5 } }` with
    /// `ensures result >= 1`: VERIFIED with a kernel-checked certificate, though
    /// trust-ir's own interpreter takes the FIRST matching case and returns 0.
    #[test]
    fn duplicate_switch_case_values_decline() {
        let module = switch_case_module(vec![Constant::Int(0), Constant::Int(0)]);
        let decline = lower(&module).expect_err("two cases cannot carry one value");
        assert!(decline.reason().contains("SAME value"), "{decline}");
        assert!(
            decline.reason().contains("first matching case"),
            "{decline}"
        );

        // Bool selectors are the same defect with two values to collide.
        let mut boolean = switch_case_module(vec![Constant::Bool(true), Constant::Bool(true)]);
        boolean.functions[0].blocks[0].params[0].1 = Ty::Bool;
        boolean.func_types[0].params[0] = Ty::Bool;
        assert!(lower(&boolean).is_err(), "duplicate Bool cases");

        // CONTROL: distinct values are mutually exclusive and lower.
        let control = switch_case_module(vec![Constant::Int(0), Constant::Int(1)]);
        lower(&control).expect("distinct case values lower");
    }

    /// REGRESSION, adversarial review round 3 (F2/F3): an integer constant
    /// outside the sort it is used at.
    ///
    /// trust-ir's reference semantics MASK it (`InterpretInt::from_i128`), so
    /// `256` at `u8` IS `0` and `200` at `i8` IS `-56`. Emitting the literal as
    /// written makes an equality nothing of that sort satisfies: as a `Switch`
    /// case value it drops the arm the program actually takes, and as an
    /// `Inst::Const` it kills the block that defines the value. Probed both
    /// ways, each VERIFIED with a certificate against a clause that is false
    /// under the IR's own interpreter. F2 is now also refused by trust-ir's FULL
    /// validator (its shared switch-literal contract types every case value), so
    /// this direct test is the lane's own gate; it used to be the only one for a
    /// `SwitchCase.value`.
    #[test]
    fn an_integer_constant_outside_its_declared_width_declines() {
        // (1) As a `Switch` case value, at both signednesses.
        let mut wide = switch_case_module(vec![Constant::Int(4_294_967_296), Constant::Int(1)]);
        let decline = lower(&wide).expect_err("2^32 is not a u32");
        assert!(decline.reason().contains("does not fit"), "{decline}");
        assert!(decline.reason().contains("MASKS"), "{decline}");

        wide.functions[0].blocks[0].params[0].1 = Ty::I8;
        wide.func_types[0].params[0] = Ty::I8;
        match &mut wide.functions[0].blocks[0].body[2].inst {
            Inst::Switch { cases, .. } => cases[0].value = Constant::Int(200),
            other => panic!("the entry terminator is a Switch, got {other:?}"),
        }
        assert!(lower(&wide).is_err(), "200 is not an i8 (it masks to -56)");

        // (2) As an `Inst::Const`, which is the same contradiction one level in.
        let (mut module, _) =
            inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        module.functions[0].blocks[0].body[0] = InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(-1),
        })
        .with_result(v(1));
        assert!(lower(&module).is_err(), "-1 is not a u64");

        // CONTROL: the bounds themselves are inclusive of the extremes.
        assert!(int_fits(255, false, 8));
        assert!(!int_fits(256, false, 8));
        assert!(int_fits(127, true, 8));
        assert!(!int_fits(128, true, 8));
        assert!(int_fits(-128, true, 8));
        assert!(!int_fits(-129, true, 8));
        assert!(int_fits(i128::MAX, false, 128));
        assert!(int_fits(i128::MIN, true, 128));
        assert!(!int_fits(-1, false, 64));
    }

    /// REGRESSION, adversarial review round 3 (F4): one `ValueId` defined twice.
    ///
    /// Two `pc$b => v == k` equations for one variable contradict whenever the
    /// two `k` disagree, which erases that path. Round 2's probe put the
    /// duplicate in the ENTRY block, where the contradiction is GLOBAL and the
    /// engine's `VacuousTruth` detector caught it; moving it onto a conditional
    /// arm defeats that detector entirely, so the gate is on the definition
    /// itself rather than on the verdict.
    #[test]
    fn a_value_defined_twice_declines() {
        let (mut module, _) =
            inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        module.functions[0].blocks[0].body.insert(
            2,
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(3),
            })
            .with_result(v(2)),
        );
        let decline = lower(&module).expect_err("value 2 is defined twice");
        assert!(
            decline.reason().contains("defined more than once"),
            "{decline}"
        );
    }

    /// REGRESSION, adversarial review round 3: the GENERAL case of the previous
    /// gate — a value used before anything defines it.
    ///
    /// The lane declares every value up front, so a definition may name a value
    /// defined later, including itself: `v == v + 1` is unsatisfiable at every
    /// width, and a mutually-recursive pair does it without either one naming
    /// itself. Same erased path, same false `Discharged`, no duplicate
    /// definition anywhere. Valid SSA always passes, because a definition
    /// dominates its uses and a dominator precedes in every topological order.
    #[test]
    fn a_value_used_before_it_is_defined_declines() {
        let (mut module, _) =
            inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        // `v2 = v2 + v1` — the sum defines the value it reads.
        module.functions[0].blocks[0].body[1] = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U64,
            lhs: v(2),
            rhs: v(1),
        })
        .with_result(v(2));
        let decline = lower(&module).expect_err("v2 reads itself");
        assert!(decline.reason().contains("before anything"), "{decline}");
        assert!(decline.reason().contains("BinOp"), "{decline}");

        // A cycle through TWO values, with every value defined exactly once.
        let (mut cycle, _) =
            inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        cycle.functions[0].blocks[0].body[0] = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U64,
            lhs: v(2),
            rhs: v(0),
        })
        .with_result(v(1));
        assert!(lower(&cycle).is_err(), "v1 and v2 define each other");
    }

    /// REGRESSION, adversarial review round 1: a terminator with TWO edges into
    /// the SAME block binds each edge to ITS OWN argument list.
    ///
    /// This shape produced a false `Discharged`. Resolving the block arguments
    /// by TARGET bound both edges to the first list found, so the phi assumption
    /// `pc$p && guard => param == arg` asserted something false in the program,
    /// and under an inconsistent assumption set every obligation is provable.
    /// The probe was `fn clamp(x: u32) -> u32` rewritten as one
    /// `CondBr x > 10 ? join([10]) : join([x])`, where `ensures result == 10`
    /// verified although the program returns `x` on the else edge.
    #[test]
    fn two_edges_into_one_block_bind_their_own_arguments() {
        // `if x > 10 { join(10) } else { join(x) }` — one terminator, one target.
        let mut function = Function::new(FuncId::new(0), "clamp", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::U32));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(10),
            })
            .with_result(v(1)),
        );
        entry.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ugt,
                ty: Ty::U32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: v(2),
            then_target: b(1),
            then_args: vec![v(1)],
            else_target: b(1),
            else_args: vec![v(0)],
        }));
        let mut join = Block::new(b(1));
        join.params.push((v(3), Ty::U32));
        join.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        function.blocks.extend([entry, join]);
        function.value_names = Some(vec![(v(0), "x".to_string())]);
        let module = module_with(
            function,
            FuncTy {
                params: vec![Ty::U32],
                returns: vec![Ty::U32],
                is_vararg: false,
                abi: None,
            },
        );
        let relation = lower(&module).expect("a diamond-free two-edge join lowers");

        let phis: Vec<&TrustExpr> = relation
            .assumptions
            .iter()
            .filter(|(id, _)| id.contains("phi"))
            .map(|(_, predicate)| predicate)
            .collect();
        assert_eq!(phis.len(), 2, "one binding per EDGE: {phis:?}");
        let rendered: Vec<String> = phis.iter().map(|phi| format!("{phi:?}")).collect();
        // The then edge (guard `v2`) binds the join parameter to the CONSTANT's
        // value; the else edge (guard `!v2`) binds it to `x`. Binding both to
        // the same argument is exactly the false assumption under review.
        assert!(
            rendered
                .iter()
                .any(|phi| !phi.contains("Not {") && phi.contains("\"v1\"")),
            "the then edge binds the constant: {rendered:?}"
        );
        assert!(
            rendered
                .iter()
                .any(|phi| phi.contains("Not {") && phi.contains("\"x\"")),
            "the else edge binds the parameter: {rendered:?}"
        );
        assert_ne!(rendered[0], rendered[1]);
    }

    /// The same shape through a `Switch`: a case and the default sharing one
    /// target, with different arguments. The probe was `match x { 1 => 10, _ =>
    /// x }` proving `ensures result == x`, false at `x = 1`.
    #[test]
    fn a_switch_case_and_default_sharing_a_target_bind_their_own_arguments() {
        let mut function = Function::new(FuncId::new(0), "pick", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::U32));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(10),
            })
            .with_result(v(1)),
        );
        entry.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(1),
            default_args: vec![v(0)],
            cases: vec![SwitchCase {
                value: Constant::Int(1),
                target: b(1),
                args: vec![v(1)],
            }],
            exhaustive_enum_unreachable: false,
        }));
        let mut join = Block::new(b(1));
        join.params.push((v(2), Ty::U32));
        join.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        function.blocks.extend([entry, join]);
        function.value_names = Some(vec![(v(0), "x".to_string())]);
        let module = module_with(
            function,
            FuncTy {
                params: vec![Ty::U32],
                returns: vec![Ty::U32],
                is_vararg: false,
                abi: None,
            },
        );
        let relation = lower(&module).expect("a switch join lowers");
        let rendered: Vec<String> = relation
            .assumptions
            .iter()
            .filter(|(id, _)| id.contains("phi"))
            .map(|(_, predicate)| format!("{predicate:?}"))
            .collect();
        assert_eq!(rendered.len(), 2, "one binding per EDGE: {rendered:?}");
        assert_ne!(rendered[0], rendered[1]);
    }

    /// A body that reads its parameter through a type outside the fragment is
    /// refused at the signature, before any instruction is looked at.
    #[test]
    fn a_non_scalar_parameter_declines() {
        let mut function = Function::new(FuncId::new(0), "takes_ref", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::Ref(Box::new(Ty::U64))));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(entry);
        let module = module_with(
            function,
            FuncTy {
                params: vec![Ty::Ref(Box::new(Ty::U64))],
                returns: vec![],
                is_vararg: false,
                abi: None,
            },
        );
        let decline = lower(&module).expect_err("a reference parameter is not scalar");
        assert!(decline.reason().contains("Ref"), "{decline}");
    }

    // -----------------------------------------------------------------------
    // REGRESSION, adversarial review round 2
    // -----------------------------------------------------------------------

    fn module_with_functions(functions: Vec<Function>, func_types: Vec<FuncTy>) -> Module {
        let mut module = Module::new("probe");
        module.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
        module.func_types = func_types;
        module.functions = functions;
        module
    }

    /// A producer value name spelled `_0` is the RETURN PLACE's name.
    ///
    /// `declare_values` wrote the parameter into `relation.variables` under its
    /// own spelling and then wrote `RESULT_VAR` over the top, so the parameter
    /// and the return place became ONE unit variable and `lower_return`'s
    /// `pc$b => _0 == <returned>` pinned the parameter to the returned value —
    /// an assumption FALSE in the program. For `fn inc(x) { x + 1 }` with `x`
    /// spelled `_0` it is also INCONSISTENT (`_0 == _0 + 1`), and an
    /// inconsistent assumption set proves every obligation.
    #[test]
    fn a_value_carrying_the_return_place_name_declines() {
        let (mut module, _) =
            inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        module.functions[0].value_names = Some(vec![(v(0), RESULT_VAR.to_string())]);
        let decline = lower(&module).expect_err("`_0` is the return place, not a value name");
        assert!(decline.reason().contains(RESULT_VAR), "{decline}");
        assert!(decline.reason().contains("reserved"), "{decline}");
    }

    /// The same collision one namespace over: a producer value named `pc$0` IS
    /// block 0's path-condition variable, so `pc_entry` (`pc$0 == true`) forced
    /// the producer's own value true. Reachable through a hand-built or
    /// replayed bundle rather than Rust source — `$` is not a Rust identifier
    /// character, and nothing downstream of the producer checked.
    #[test]
    fn a_value_in_the_path_condition_namespace_declines() {
        let (mut module, _) =
            inc_function(vec![InstrNode::new(Inst::Return { values: vec![v(2)] })]);
        module.functions[0].value_names = Some(vec![(v(0), "pc$0".to_string())]);
        let decline = lower(&module).expect_err("`pc$0` is block 0's path condition");
        assert!(decline.reason().contains("pc$0"), "{decline}");
        assert!(decline.reason().contains("reserved"), "{decline}");
    }

    fn cast_function(op: CastOp, src: Ty, dst: Ty) -> Module {
        let mut function = Function::new(FuncId::new(0), "convert", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), src.clone()));
        entry.body.push(
            InstrNode::new(Inst::Cast {
                op,
                src_ty: src.clone(),
                dst_ty: dst.clone(),
                operand: v(0),
            })
            .with_result(v(1)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        function.blocks.push(entry);
        function.value_names = Some(vec![(v(0), "x".to_string())]);
        module_with_functions(
            vec![function],
            vec![FuncTy {
                params: vec![src],
                returns: vec![dst],
                is_vararg: false,
                abi: None,
            }],
        )
    }

    /// `CastOp` is not decoration: the boundary expression's `Cast` derives its
    /// extension from the SOURCE sort's signedness, so `SExt` from an unsigned
    /// source was modelled as a ZERO extension (and `ZExt` from a signed source
    /// as a sign extension). trust-ir's own interpreter reads the operand's raw
    /// bits in two's complement for `SExt` regardless of the source type's
    /// signedness, so `200u8 as i32` is `-56`, not `200`. The op and the sort
    /// must AGREE or the cast is refused.
    #[test]
    fn a_cast_whose_op_disagrees_with_its_source_sort_declines() {
        // (op, src, dst, the needle a decline must carry — `None` means it lowers)
        let cases: Vec<(CastOp, Ty, Ty, Option<&str>)> = vec![
            // The two the encoder would model as the OTHER extension.
            (CastOp::SExt, Ty::U8, Ty::I32, Some("SExt")),
            (CastOp::SExt, Ty::U16, Ty::I64, Some("SExt")),
            (CastOp::ZExt, Ty::I8, Ty::I32, Some("ZExt")),
            // `SExt` from `Bool` sets every destination bit; the pre-existing
            // carve-out stays.
            (CastOp::SExt, Ty::Bool, Ty::I32, Some("SExt")),
            // A `Trunc` that does not narrow would be encoded as an EXTENSION,
            // because the encoder chooses by comparing widths.
            (CastOp::Trunc, Ty::U8, Ty::U32, Some("Trunc")),
            (CastOp::ZExt, Ty::U32, Ty::U8, Some("ZExt")),
            // What remains expressible, exactly.
            (CastOp::SExt, Ty::I8, Ty::I32, None),
            (CastOp::ZExt, Ty::U8, Ty::U32, None),
            (CastOp::ZExt, Ty::Bool, Ty::U32, None),
            (CastOp::Trunc, Ty::U32, Ty::U8, None),
            (CastOp::Trunc, Ty::I32, Ty::I8, None),
        ];
        for (op, src, dst, needle) in cases {
            let module = cast_function(op, src.clone(), dst.clone());
            match (lower(&module), needle) {
                (Ok(_), None) => {}
                (Err(decline), Some(needle)) => assert!(
                    decline.reason().contains(needle),
                    "decline for {op:?} {src:?} -> {dst:?} must name it, got: {decline}"
                ),
                (Ok(_), Some(needle)) => {
                    panic!("{op:?} {src:?} -> {dst:?} must decline naming {needle}")
                }
                (Err(decline), None) => {
                    panic!("{op:?} {src:?} -> {dst:?} is expressible, got: {decline}")
                }
            }
        }
    }

    /// The shadowing gate existed only for the function being lowered. Two
    /// CALLEE parameters sharing one source name silently bound the callee's
    /// published `ensures` to the WRONG caller argument (last insert won), so
    /// the caller assumed something false about its own arguments.
    #[test]
    fn a_callee_with_two_parameters_sharing_a_name_declines() {
        // BOTH of `g`'s parameters carry the source name `a`, so `ensures
        // result == a` bound to whichever caller argument was written last.
        let mut module =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "a".to_string())]);
        push_established_callee_ensures(&mut module);
        let decline = lower(&module).expect_err("an ambiguous callee parameter name");
        assert!(decline.reason().contains("ambiguous"), "{decline}");
        assert!(decline.reason().contains('a'), "{decline}");
    }

    /// THE POSITIVE CONTROL for the two gates above: a callee whose parameters
    /// carry DISTINCT names still lowers, and its `ensures` binds to the
    /// argument the contract actually names — the first, not the last one
    /// written. Without this, "decline everything" would pass the pair.
    #[test]
    fn a_callee_with_distinct_parameter_names_binds_the_right_argument() {
        let mut module =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
        push_established_callee_ensures(&mut module);
        let relation = lower(&module).expect("distinct callee parameter names lower");
        let ensures: Vec<String> = relation
            .assumptions
            .iter()
            .filter(|(id, _)| id.contains("callee_ensures"))
            .map(|(_, predicate)| format!("{predicate:?}"))
            .collect();
        assert_eq!(ensures.len(), 1, "{ensures:?}");
        // `ensures result == a` is about the callee's FIRST parameter, which the
        // caller passes `x` to. Binding it to `y` is the defect under review.
        assert!(ensures[0].contains("\"x\""), "{ensures:?}");
        assert!(!ensures[0].contains("\"y\""), "{ensures:?}");

        // DISCLOSURE (adversarial review round 3, minor): the callee is read
        // CONTRACT-ONLY at this pin, so an outcome that used its `ensures` rests
        // on a claim trust-vc did not check — a contract false about its own
        // body hands the caller a fact the program never establishes, and a
        // CONTRADICTORY one kills the call's path outright. The premise is what
        // tells a consumer that, so it is asserted rather than assumed present.
        let callee_contract: Vec<&TrustVcNativeTrustIrPremise> = relation
            .premises
            .iter()
            .filter(|premise| premise.kind() == TrustVcNativeTrustIrPremiseKind::CalleeContract)
            .collect();
        assert_eq!(callee_contract.len(), 1, "{:?}", relation.premises);
        assert!(
            callee_contract[0].detail().contains("`g`"),
            "the premise must name the callee it trusted: {:?}",
            callee_contract[0]
        );

        // ROUND 8, MINOR: the premise must carry a value DERIVED from the check,
        // not a sentence about it. These digests are recomputed here from the
        // module the test built; a premise that merely SAID "lineage-bound
        // `CleanCic` certificate" would pass the assertion above and fail these.
        //
        // DISCRIMINATING: replace `established_callee_ensures`'s return value
        // with the pre-round-8 fixed text and exactly this block fails.
        let ensures_row = module
            .proof_obligations
            .iter()
            .find(|obligation| obligation.id == ProofId::new(0))
            .expect("the callee `ensures` row");
        let lineage = trust_ir::proof::clean_cic_lineage_digest(ensures_row);
        let term = match &module.proof_certificates[0].evidence {
            trust_ir::ProofEvidence::CleanCic { term, .. } => term.clone(),
            other => panic!("the fixture certificate is a `CleanCic` term: {other:?}"),
        };
        let detail = callee_contract[0].detail();
        assert!(
            detail.contains(&lineage.to_string()),
            "the premise must quote the lineage digest the check matched: {detail}"
        );
        assert!(
            detail.contains(&crate::native_trust_ir_bundle::sha256_hex(&term)),
            "the premise must quote the digest of the term the producer re-checked: {detail}"
        );
        assert!(
            detail.contains(&module.proof_certificates[0].stable_digest().to_string()),
            "the premise must name the certificate it found: {detail}"
        );
    }

    /// ROUND-5 BLOCKER, at the lowering seam: a callee contract the producer has
    /// not established is never assumed, whatever its formula says. `Failed` is
    /// a contract the producer explicitly did NOT prove; `Pending` is one it has
    /// not proved yet; `Trusted` is faith, which this crate already refuses as
    /// certificate authority.
    #[test]
    fn a_callee_contract_at_an_unestablished_status_declines() {
        for status in [
            ProofStatus::Pending,
            ProofStatus::Failed,
            ProofStatus::Trusted,
            // ROUND 6: `Discharged` joined them. See
            // `a_callee_ensures_at_a_bare_discharged_label_is_not_evidence`.
            ProofStatus::Discharged,
        ] {
            let mut module =
                two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
            module
                .proof_obligations
                .push(callee_ensures_result_eq_a_at(status));
            let decline =
                lower(&module).expect_err("an unestablished callee contract must never be assumed");
            assert!(
                decline.reason().contains("only `Certified` is EVIDENCE"),
                "{status:?}: {decline}"
            );
            assert!(
                decline.reason().contains(&format!("{status:?}")),
                "the decline must name the status it refused on: {decline}"
            );
        }

        // The positive control: the same row at `Certified` WITH the
        // lineage-bound certificate the status is supposed to stand for.
        let mut certified =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
        push_established_callee_ensures(&mut certified);
        let relation = lower(&certified).expect("a `Certified` callee contract is established");
        assert_eq!(
            relation
                .assumptions
                .iter()
                .filter(|(id, _)| id.contains("callee_ensures"))
                .count(),
            1
        );
    }

    /// `fn f(x: u32, y: u32) -> u32 { g(x, y) }` with `g` taking two `u32`
    /// parameters under the given names.
    fn two_parameter_call_module(callee_names: Vec<(ValueId, String)>) -> Module {
        let mut caller = Function::new(FuncId::new(0), "f", FuncTyId::new(0), b(0));
        let mut caller_entry = Block::new(b(0));
        caller_entry.params.push((v(0), Ty::U32));
        caller_entry.params.push((v(1), Ty::U32));
        caller_entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        caller_entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        caller.blocks.push(caller_entry);
        caller.value_names = Some(vec![(v(0), "x".to_string()), (v(1), "y".to_string())]);

        let mut callee = Function::new(FuncId::new(1), "g", FuncTyId::new(1), b(0));
        let mut callee_entry = Block::new(b(0));
        callee_entry.params.push((v(0), Ty::U32));
        callee_entry.params.push((v(1), Ty::U32));
        callee_entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        callee.blocks.push(callee_entry);
        callee.value_names = Some(callee_names);

        let two_u32 = FuncTy {
            params: vec![Ty::U32, Ty::U32],
            returns: vec![Ty::U32],
            is_vararg: false,
            abi: None,
        };
        module_with_functions(vec![caller, callee], vec![two_u32.clone(), two_u32])
    }

    /// ROUND-6 BLOCKER 1, at the seam: a bare `Discharged` LABEL is not
    /// evidence, and the carve-out in `validate_producer_module` is exactly why.
    ///
    /// At the pinned rev `validate_discharged_authority` raises
    /// `DischargedWithoutCertificate` for EVERY `Discharged` row with no
    /// authority-admitted certificate — unconditionally, under the rejecting
    /// authority this crate passes. That verdict is carried past the input gate
    /// on purpose (the import/merge grading path needs it), so a `Discharged`
    /// row backed by NOTHING reaches this lane. Reading it as established is
    /// precisely what upstream's own error text forbids.
    #[test]
    fn a_callee_ensures_at_a_bare_discharged_label_is_not_evidence() {
        let mut module =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
        module
            .proof_obligations
            .push(callee_ensures_result_eq_a_at(ProofStatus::Discharged));
        let decline = lower(&module)
            .expect_err("a `Discharged` label with no certificate is not proof authority");
        assert!(decline.reason().contains("Certified"), "{decline}");
        assert!(decline.reason().contains("Discharged"), "{decline}");
    }

    /// ROUND-6 BLOCKER 1, second half: `Certified` is only meaningful because a
    /// certificate is actually bound to the row. A `Certified` STATUS with no
    /// `CleanCic` certificate in the module is the same bare label one tier up.
    #[test]
    fn a_certified_callee_ensures_with_no_certificate_declines() {
        let mut module =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
        module
            .proof_obligations
            .push(callee_ensures_result_eq_a_at(ProofStatus::Certified));
        let decline =
            lower(&module).expect_err("a `Certified` label with no certificate is not evidence");
        assert!(decline.reason().contains("CleanCic"), "{decline}");
    }

    /// ROUND-6 BLOCKER 2: a callee `requires` carrying an `ObligationSite`
    /// bypassed the call-site-precondition guard entirely.
    ///
    /// The old selection filtered the callee's rows with `site.is_none()` BEFORE
    /// looking for a `Precondition`, so a sited `requires` never entered the
    /// collection the guard scanned: the `requires` was silently dropped and the
    /// `ensures` assumed unconditionally. Such a row is WELL-FORMED to the
    /// producer validator, which only requires that the site resolve to a real
    /// instruction in the obligation's own function.
    ///
    /// Independent of blocker 1 — the `ensures` here is `Certified` AND backed
    /// by a lineage-bound certificate, so the status gate is satisfied and this
    /// test measures the selection and nothing else. The control is the same
    /// module with `site: None`, which declines on the guard.
    #[test]
    fn a_callee_precondition_anchored_at_a_site_still_declines() {
        for site in [
            None,
            Some(ObligationSite {
                function: FuncId::new(1),
                block: b(0),
                inst_index: 0,
            }),
        ] {
            let mut module =
                two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
            let ensures = callee_ensures_result_eq_a_at(ProofStatus::Certified);
            module.proof_certificates.push(clean_cic_for(&ensures));
            module.proof_obligations.push(ensures);

            let requires = ProofObligation::new(
                ProofId::new(1),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "g requires",
            )
            .with_function(FuncId::new(1))
            .with_formula(trust_ir::ProofFormula::new(
                "trust-types.Formula@1",
                r#"{"formula":{"Ge":[{"Var":["a","Int"]},{"Int":1}]}}"#,
            ));
            let requires = match site {
                Some(site) => requires.with_site(site),
                None => requires,
            };
            module.proof_obligations.push(requires);

            let Err(decline) = lower(&module) else {
                panic!("a callee precondition is the caller's to discharge, at site {site:?}");
            };
            assert!(
                decline.reason().contains("precondition"),
                "{site:?}: {decline}"
            );
        }
    }

    /// ROUND-7 MAJOR 1: the kernel that is this lane's AUTHORITY for an imported
    /// `ensures` and the decoder that actually assumes it read TWO DIFFERENT
    /// producer-supplied fields.
    ///
    /// `trust_ir::clean_expr_lowering::contract::predicate_text` — the grounding
    /// used by the `Certified` re-check — is
    /// `formula.smtlib.as_deref().unwrap_or(&formula.payload)`, i.e. it PREFERS
    /// `smtlib`. This lane decodes `formula.payload` and nothing else. Nothing
    /// upstream binds the two renderings to each other: the lineage digest
    /// covers both bytes but never compares them, so a producer may ship a
    /// trivially-true `smtlib` for the kernel and an arbitrary `payload` for the
    /// consumer, at a matching lineage.
    #[test]
    fn a_callee_ensures_whose_smtlib_and_payload_are_two_formulas_declines() {
        let mut module =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
        let mut ensures = callee_ensures_result_eq_a_at(ProofStatus::Certified);
        // What the Clean kernel would be handed: a closed tautology.
        ensures.formula.as_mut().expect("formula").smtlib = Some("(>= _0 0)".to_string());
        // The lineage is DERIVED after the divergence, exactly as a hostile
        // producer would emit it — so the identity check still matches.
        module.proof_certificates.push(clean_cic_for(&ensures));
        module.proof_obligations.push(ensures);

        let decline = lower(&module).expect_err(
            "the kernel grounds `smtlib` and this lane decodes `payload`; nothing binds them",
        );
        assert!(decline.reason().contains("smtlib"), "{decline}");
    }

    /// The same row with the SAME bytes in both renderings is the one shape
    /// where the kernel's goal and this lane's assumption are the same object,
    /// so it must still be importable. The control that keeps the rule above
    /// from being "refuse everything".
    #[test]
    fn a_callee_ensures_whose_smtlib_repeats_the_payload_still_imports() {
        let mut module =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
        let mut ensures = callee_ensures_result_eq_a_at(ProofStatus::Certified);
        let payload = ensures.formula.as_ref().expect("formula").payload.clone();
        ensures.formula.as_mut().expect("formula").smtlib = Some(payload);
        module.proof_certificates.push(clean_cic_for(&ensures));
        module.proof_obligations.push(ensures);

        lower(&module).expect("one rendering, spelled twice, is still one formula");
    }

    /// ROUND-7 MAJOR 2: blocker 2 AS A CLASS. `obligation.function` was still a
    /// silent pre-filter on the callee-contract selection, one field over from
    /// the `site` filter round 6 inverted.
    ///
    /// Upstream `validate_obligation_sites` checks scope/site agreement only
    /// "when both are present", so a `Precondition` with `function: None` and an
    /// `ObligationSite` pointing INSIDE the callee is well-formed to the
    /// producer validator. The old selection asked only `function ==
    /// Some(callee)`, so the row never entered the adjudication, the `requires`
    /// was silently dropped, and the callee's `ensures` was imported unguarded.
    ///
    /// The second case is the row that is attributed to NOBODY: it cannot be
    /// excluded from being the callee's `requires` either, so it declines too.
    ///
    /// ROUND 8, MAJOR 2(a) — WHAT THIS TEST DOES AND DOES NOT MEASURE, recorded
    /// because round 7's report claimed otherwise. Both cases here carry
    /// `function: None`, so both land in the `Unattributed` arm under the
    /// round-7 implementation AND under a function-only one; reducing
    /// [`RowAttribution::of`] to the pre-round-7 function-only test leaves this
    /// test PASSING. MEASURED in round 8, and the round-7 report's claim that
    /// the neutralization made it fail was simply not run. The test is kept: it
    /// pins that an unscoped callee precondition declines, which is a real
    /// property. The `site.function` half is measured by
    /// `a_precondition_sited_in_a_third_function_does_not_decline_the_call`, and
    /// the call-site rule by
    /// `a_precondition_anchored_at_the_call_is_the_callees_whatever_it_is_scoped_to`
    /// — each with a neutralization that was RUN.
    #[test]
    fn a_callee_precondition_the_producer_did_not_scope_still_declines() {
        for (label, function, site) in [
            (
                "sited at the callee, unscoped",
                None,
                Some(ObligationSite {
                    function: FuncId::new(1),
                    block: b(0),
                    inst_index: 0,
                }),
            ),
            ("neither scoped nor sited", None, None),
        ] {
            let mut module =
                two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
            push_established_callee_ensures(&mut module);

            let mut requires = ProofObligation::new(
                ProofId::new(1),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "g requires",
            )
            .with_formula(trust_ir::ProofFormula::new(
                "trust-types.Formula@1",
                r#"{"formula":{"Ge":[{"Var":["a","Int"]},{"Int":1}]}}"#,
            ));
            requires.function = function;
            if let Some(site) = site {
                requires = requires.with_site(site);
            }
            module.proof_obligations.push(requires);

            let Err(decline) = lower(&module) else {
                panic!(
                    "{label}: an unscoped callee precondition is still the caller's to discharge"
                );
            };
            assert!(
                decline.reason().contains("precondition"),
                "{label}: {decline}"
            );
        }
    }

    /// ROUND 8, MAJOR 1 — A CALL-SITE PRECONDITION IS THE CALLEE'S, whichever
    /// function it is scoped to.
    ///
    /// [`ObligationSite`]'s own doc says `site` names the `(block, inst_index)`
    /// of the instruction whose check the obligation states — and a call-site
    /// precondition VC lives in the CALLER. So `function` and `site.function`
    /// both name the caller, the row was classified
    /// [`RowAttribution::AnotherFunction`], `callee_contract_facts` skipped it
    /// before adjudication, and the callee's `ensures` was imported WITH NO
    /// GUARD: never used as a guard, never recorded in the
    /// `UnimportedCalleeObligation` premise, and never discharged (E3 declines
    /// every sited row as a requested row). Nobody owed it.
    ///
    /// DISCRIMINATING: reverting `RowAttribution::of` to the pre-round-8 body
    /// (delete the `obligation.site` block at the top) makes exactly this test
    /// fail — `lower` succeeds and the `ensures` is imported. MEASURED, not
    /// assumed; round 7 reported a neutralization it had not run, and its test
    /// could not have failed under it.
    #[test]
    fn a_precondition_anchored_at_the_call_is_the_callees_whatever_it_is_scoped_to() {
        for (label, function) in [
            ("scoped to the CALLER", Some(FuncId::new(0))),
            ("scoped to nothing", None),
        ] {
            let mut module =
                two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
            push_established_callee_ensures(&mut module);

            let mut requires = ProofObligation::new(
                ProofId::new(1),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "g requires, as a VC at f's call",
            )
            .with_formula(trust_ir::ProofFormula::new(
                "trust-types.Formula@1",
                r#"{"formula":{"Ge":[{"Var":["x","Int"]},{"Int":1}]}}"#,
            ))
            // THE CALL INSTRUCTION in the caller: `f`'s block 0, instruction 0.
            .with_site(ObligationSite {
                function: FuncId::new(0),
                block: b(0),
                inst_index: 0,
            });
            requires.function = function;
            module.proof_obligations.push(requires);

            let Err(decline) = lower(&module) else {
                panic!("{label}: a precondition anchored AT THE CALL is the callee's to guard");
            };
            assert!(
                decline.reason().contains("precondition"),
                "{label}: {decline}"
            );
            assert!(
                decline.reason().contains("CALLS `g`"),
                "{label}: the decline must say WHY the row is the callee's: {decline}"
            );
        }
    }

    /// The same rule one call over: a precondition anchored at a DIFFERENT call
    /// to the same callee still evidences that the callee has a `requires`, and
    /// importing its `ensures` unguarded here would rest on a guard nothing
    /// established at THIS call.
    ///
    /// DISCRIMINATING: narrowing [`RowAttribution::of`] to
    /// `call.names(site)` — the literal "this call instruction" reading — makes
    /// exactly this test fail.
    #[test]
    fn a_precondition_anchored_at_another_call_to_the_same_callee_also_declines() {
        let mut module = two_parameter_call_module_with_second_caller();
        push_established_callee_ensures(&mut module);
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "g requires, as a VC at h's call",
            )
            .with_function(FuncId::new(2))
            .with_formula(trust_ir::ProofFormula::new(
                "trust-types.Formula@1",
                r#"{"formula":{"Ge":[{"Var":["p","Int"]},{"Int":1}]}}"#,
            ))
            // `h`'s call to `g`, not `f`'s.
            .with_site(ObligationSite {
                function: FuncId::new(2),
                block: b(0),
                inst_index: 0,
            }),
        );
        let decline = lower(&module)
            .expect_err("a `requires` of `g` anchored at any call to `g` is still `g`'s");
        assert!(decline.reason().contains("CALLS `g`"), "{decline}");
    }

    /// THE POSITIVE EXCLUSION THE `site.function` HALF ACTUALLY PERFORMS.
    ///
    /// ROUND 8, MAJOR 2(b): before this test, the `site.function` half of
    /// [`RowAttribution::of`] had NO discriminating test at all — every shape
    /// that exercised it landed in the same arm under a function-only
    /// implementation, and its only measurable effect through the product entry
    /// point was to make the lane MORE permissive. A guard with no
    /// discriminating test is either untested or unjustified.
    ///
    /// Here is its job, stated positively and tested: a row the producer scoped
    /// to NOTHING but anchored at an instruction inside a THIRD function, which
    /// is not a call to this callee, is positively someone else's. Include-by-
    /// default is not "refuse on sight of any precondition anywhere".
    ///
    /// DISCRIMINATING: making `sited` always `None` in
    /// [`RowAttribution::of`] makes this row `Unattributed`, which is
    /// adjudicated, and exactly this test fails.
    #[test]
    fn a_precondition_sited_in_a_third_function_does_not_decline_the_call() {
        let mut module = two_parameter_call_module_with_second_caller();
        push_established_callee_ensures(&mut module);
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "a per-check VC inside `h`",
            )
            .with_formula(trust_ir::ProofFormula::new(
                "trust-types.Formula@1",
                r#"{"formula":{"Ge":[{"Var":["p","Int"]},{"Int":1}]}}"#,
            ))
            // `h`'s RETURN, which is not a call to anything.
            .with_site(ObligationSite {
                function: FuncId::new(2),
                block: b(0),
                inst_index: 1,
            }),
        );
        lower(&module).expect(
            "a row anchored at a non-call instruction in a third function is
             positively that function's",
        );
    }

    /// A site that resolves to NO instruction, and a site that resolves to a
    /// `CallIndirect`, are both adjudicated rather than excluded: nothing can be
    /// concluded from a position that names no direct call — including that it
    /// is not this callee's.
    #[test]
    fn a_site_that_names_no_direct_call_is_adjudicated_not_skipped() {
        for (label, site) in [
            (
                "out of range",
                ObligationSite {
                    function: FuncId::new(2),
                    block: b(0),
                    inst_index: 99,
                },
            ),
            (
                "a function that is not in the module",
                ObligationSite {
                    function: FuncId::new(9),
                    block: b(0),
                    inst_index: 0,
                },
            ),
        ] {
            let mut module = two_parameter_call_module_with_second_caller();
            push_established_callee_ensures(&mut module);
            module.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(1),
                    ObligationKind::Precondition,
                    ProofStatus::Pending,
                    "a requires at an unresolvable position",
                )
                .with_formula(trust_ir::ProofFormula::new(
                    "trust-types.Formula@1",
                    r#"{"formula":{"Ge":[{"Var":["p","Int"]},{"Int":1}]}}"#,
                ))
                .with_site(site),
            );
            let Err(decline) = lower(&module) else {
                panic!("{label}: an unresolvable site cannot exclude a row from being `g`'s");
            };
            assert!(
                decline
                    .reason()
                    .contains("does not resolve to a DIRECT call"),
                "{label}: {decline}"
            );
        }
    }

    /// The type the drop-shape tests drop. Any type keys the glue table.
    const DROPPED: Ty = Ty::U64;

    /// Every instruction that calls a function the module names, in the shape
    /// that calls `callee`. A drop calls its type's glue, so the drop shapes
    /// call `callee` once `DROPPED`'s glue row names it.
    fn direct_call_shapes(callee: FuncId) -> Vec<(&'static str, Inst)> {
        vec![
            (
                "CallCannotUnwind",
                Inst::CallCannotUnwind {
                    callee,
                    args: vec![v(0), v(1)],
                },
            ),
            (
                "Invoke",
                Inst::Invoke {
                    callee,
                    args: vec![v(0), v(1)],
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
            ),
            (
                "Drop",
                Inst::Drop {
                    ty: DROPPED,
                    ptr: v(0),
                },
            ),
            (
                "DropInvoke",
                Inst::DropInvoke {
                    ty: DROPPED,
                    ptr: v(0),
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
            ),
        ]
    }

    /// A callee reaching back to its caller through ANY direct-call shape is
    /// a recursion cycle, not only through a plain `Call`: the no-unwind call,
    /// the invoke, and a drop whose glue is the caller. A drop whose glue the
    /// module does not resolve could call anything, so it declines too.
    ///
    /// TWIN: the same shapes calling `g` itself (not `f`) leave `f` out of
    /// the cycle, and the call lowers.
    #[test]
    fn a_callee_reaching_its_caller_through_any_call_shape_declines() {
        let with_back_call = |inst: Inst, glue: Option<FuncId>| {
            let mut module =
                two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
            push_established_callee_ensures(&mut module);
            if let Some(glue) = glue {
                module
                    .set_drop_glue(DROPPED, glue)
                    .expect("one glue row for the dropped type");
            }
            module.functions[1].blocks[0]
                .body
                .insert(0, InstrNode::new(inst).with_result(v(2)));
            lower(&module)
        };
        for (name, inst) in direct_call_shapes(FuncId::new(0)) {
            let decline = with_back_call(inst, Some(FuncId::new(0)))
                .expect_err("`g` reaches `f` back, so `f`'s call to `g` is in a cycle");
            assert!(
                decline.reason().contains("recursion cycle"),
                "{name}: {decline}"
            );
        }
        for (name, inst) in direct_call_shapes(FuncId::new(1)) {
            with_back_call(inst, Some(FuncId::new(1)))
                .unwrap_or_else(|decline| panic!("{name}: `g` calls only itself: {decline}"));
        }
        let decline = with_back_call(
            Inst::Drop {
                ty: DROPPED,
                ptr: v(0),
            },
            None,
        )
        .expect_err("a drop with no glue row could call `f`");
        assert!(decline.reason().contains("recursion cycle"), "{decline}");
    }

    /// A precondition anchored at ANY instruction that calls `g` is `g`'s,
    /// whatever the call's unwind shape; one anchored at an indirect call of
    /// any shape, or at a drop with no glue row, names no callee and is
    /// adjudicated.
    ///
    /// TWIN: the same direct shapes in `h` calling `h` itself, not `g`, are
    /// positively `h`'s and leave the call alone.
    #[test]
    fn a_precondition_anchored_at_any_call_shape_is_attributed_by_its_callee() {
        let with_site_inst = |inst: Inst, glue: Option<FuncId>| {
            let mut module = two_parameter_call_module_with_second_caller();
            push_established_callee_ensures(&mut module);
            if let Some(glue) = glue {
                module
                    .set_drop_glue(DROPPED, glue)
                    .expect("one glue row for the dropped type");
            }
            module.functions[2].blocks[0].body[0] = InstrNode::new(inst).with_result(v(2));
            module.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(1),
                    ObligationKind::Precondition,
                    ProofStatus::Pending,
                    "a requires anchored at h's instruction 0",
                )
                .with_function(FuncId::new(2))
                .with_formula(trust_ir::ProofFormula::new(
                    "trust-types.Formula@1",
                    r#"{"formula":{"Ge":[{"Var":["p","Int"]},{"Int":1}]}}"#,
                ))
                .with_site(ObligationSite {
                    function: FuncId::new(2),
                    block: b(0),
                    inst_index: 0,
                }),
            );
            lower(&module)
        };
        for (name, inst) in direct_call_shapes(FuncId::new(1)) {
            let decline = with_site_inst(inst, Some(FuncId::new(1)))
                .expect_err("a `requires` anchored at a call of `g` is `g`'s");
            assert!(decline.reason().contains("CALLS `g`"), "{name}: {decline}");
        }
        for (name, inst) in direct_call_shapes(FuncId::new(2)) {
            with_site_inst(inst, Some(FuncId::new(2)))
                .unwrap_or_else(|decline| panic!("{name}: a call of `h` is not `g`'s: {decline}"));
        }
        let indirect = [
            (
                "CallIndirectCannotUnwind",
                Inst::CallIndirectCannotUnwind {
                    callee: v(0),
                    sig: FuncTyId::new(1),
                    args: vec![v(0), v(1)],
                    calling_conv: trust_ir::CallingConv::C,
                },
            ),
            (
                "InvokeIndirect",
                Inst::InvokeIndirect {
                    callee: v(0),
                    sig: FuncTyId::new(1),
                    args: vec![v(0), v(1)],
                    calling_conv: trust_ir::CallingConv::C,
                    normal_dest: b(1),
                    normal_args: vec![],
                    unwind_dest: b(2),
                },
            ),
            (
                "Drop without glue",
                Inst::Drop {
                    ty: DROPPED,
                    ptr: v(0),
                },
            ),
        ];
        for (name, inst) in indirect {
            let decline = with_site_inst(inst, None)
                .expect_err("a site that names no callee cannot exclude the row");
            assert!(
                decline
                    .reason()
                    .contains("does not resolve to a DIRECT call"),
                "{name}: {decline}"
            );
        }
    }

    /// `f` calls `g`; `h` calls `g` too. Two call sites for one callee, which is
    /// what the round-8 call-site attribution rules are about.
    fn two_parameter_call_module_with_second_caller() -> Module {
        let mut module =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
        let mut second_caller = Function::new(FuncId::new(2), "h", FuncTyId::new(2), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::U32));
        entry.params.push((v(1), Ty::U32));
        entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        second_caller.blocks.push(entry);
        second_caller.value_names = Some(vec![(v(0), "p".to_string()), (v(1), "q".to_string())]);
        module.functions.push(second_caller);
        module.func_types.push(FuncTy {
            params: vec![Ty::U32, Ty::U32],
            returns: vec![Ty::U32],
            is_vararg: false,
            abi: None,
        });
        module
    }

    /// The control for the rule above: a `Precondition` positively attributed to
    /// a DIFFERENT function is not the callee's, and must not decline the call.
    /// Include-by-default is not "refuse on sight of any precondition anywhere".
    #[test]
    fn a_precondition_scoped_to_another_function_does_not_decline_the_call() {
        let mut module =
            two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
        push_established_callee_ensures(&mut module);
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "f requires",
            )
            // The CALLER's own `requires`, which the call site does not owe.
            .with_function(FuncId::new(0))
            .with_formula(trust_ir::ProofFormula::new(
                "trust-types.Formula@1",
                r#"{"formula":{"Ge":[{"Var":["x","Int"]},{"Int":1}]}}"#,
            )),
        );
        lower(&module).expect("another function's precondition is not this call's guard");
    }

    /// ROUND-7 MINOR: `RefinementType` and `TypeInvariant` over a SCALAR
    /// parameter are reachable in a call this lane models, and a producer may
    /// spell a caller-owed constraint as either of them rather than as a
    /// `Precondition`. Omitting them was assertion, not argument — same
    /// fail-open direction as blocker 2. They decline.
    #[test]
    fn a_callee_refinement_or_type_invariant_row_declines_the_call() {
        for kind in [
            ObligationKind::RefinementType,
            ObligationKind::TypeInvariant,
        ] {
            let mut module =
                two_parameter_call_module(vec![(v(0), "a".to_string()), (v(1), "b".to_string())]);
            push_established_callee_ensures(&mut module);
            module.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(1),
                    kind.clone(),
                    ProofStatus::Pending,
                    "g refines",
                )
                .with_function(FuncId::new(1))
                .with_formula(trust_ir::ProofFormula::new(
                    "trust-types.Formula@1",
                    r#"{"formula":{"Ge":[{"Var":["a","Int"]},{"Int":1}]}}"#,
                )),
            );
            let Err(decline) = lower(&module) else {
                panic!("{kind:?} over a scalar parameter may be the caller's to establish");
            };
            assert!(
                decline.reason().to_lowercase().contains("caller"),
                "{kind:?}: {decline}"
            );
        }
    }

    /// A `CleanCic` certificate bound to `obligation` by the lineage digest
    /// trust-ir itself derives from the row. DERIVED, never hand-written: the
    /// digest comes from `clean_cic_lineage_digest`, the same function the
    /// validator uses.
    fn clean_cic_for(obligation: &ProofObligation) -> trust_ir::ProofCertificate {
        trust_ir::ProofCertificate {
            obligation: obligation.id,
            prover: "trust_vc".to_string(),
            evidence: trust_ir::ProofEvidence::CleanCic {
                term: vec![1],
                context: Vec::new(),
                lineage: trust_ir::proof::clean_cic_lineage_digest(obligation),
                kernel_recheck: None,
            },
            assurance: None,
        }
    }

    /// Push `g`'s published `ensures result == a` in the ONLY shape this lane
    /// accepts: `Certified`, with a lineage-bound `CleanCic` certificate.
    ///
    /// Round 5 made the status load-bearing but accepted `Discharged`. Round 6
    /// showed `Discharged` is a bare label the producer validator lets through
    /// with nothing behind it, so `Certified` plus a certificate is what an
    /// ESTABLISHED callee contract now means. `callee_ensures_result_eq_a_at`
    /// below is the same row at the statuses that must refuse.
    fn push_established_callee_ensures(module: &mut Module) {
        let ensures = callee_ensures_result_eq_a_at(ProofStatus::Certified);
        module.proof_certificates.push(clean_cic_for(&ensures));
        module.proof_obligations.push(ensures);
    }

    fn callee_ensures_result_eq_a_at(status: ProofStatus) -> ProofObligation {
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            status,
            "g ensures",
        )
        .with_function(FuncId::new(1))
        .with_formula(trust_ir::ProofFormula::new(
            "trust-types.Formula@1",
            r#"{"formula":{"Eq":[{"Var":["_0","Int"]},{"Var":["a","Int"]}]}}"#,
        ))
    }

    /// A callee parameter spelled `_0` is the same collision as the caller's,
    /// one scope over: the result binding is inserted over it, so the callee's
    /// `ensures` mentioning that parameter would resolve to the CALL's result.
    #[test]
    fn a_callee_parameter_named_like_the_return_place_declines() {
        let mut caller = Function::new(FuncId::new(0), "f", FuncTyId::new(0), b(0));
        let mut caller_entry = Block::new(b(0));
        caller_entry.params.push((v(0), Ty::U32));
        caller_entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(0)],
            })
            .with_result(v(1)),
        );
        caller_entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        caller.blocks.push(caller_entry);
        caller.value_names = Some(vec![(v(0), "x".to_string())]);

        let mut callee = Function::new(FuncId::new(1), "g", FuncTyId::new(1), b(0));
        let mut callee_entry = Block::new(b(0));
        callee_entry.params.push((v(0), Ty::U32));
        callee_entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        callee.blocks.push(callee_entry);
        callee.value_names = Some(vec![(v(0), RESULT_VAR.to_string())]);

        let module = module_with_functions(
            vec![caller, callee],
            vec![
                FuncTy {
                    params: vec![Ty::U32],
                    returns: vec![Ty::U32],
                    is_vararg: false,
                    abi: None,
                },
                FuncTy {
                    params: vec![Ty::U32],
                    returns: vec![Ty::U32],
                    is_vararg: false,
                    abi: None,
                },
            ],
        );
        let decline = lower(&module).expect_err("a callee parameter named `_0`");
        assert!(decline.reason().contains(RESULT_VAR), "{decline}");
        assert!(decline.reason().contains("reserved"), "{decline}");
    }

    /// `successor_ids` and `collect_edges` read `body.last()` rather than
    /// trust-ir's own `Block::terminator()`, and nothing rejected a terminator
    /// sitting mid-body. A block whose real terminator is followed by a dead
    /// `Return` had its branch silently IGNORED and the dead `Return` read as
    /// the terminator, so the lane modelled a different CFG than the module
    /// declares. `NativeVerificationBundle::validate()` does not reject the
    /// shape (only trust-ir-build's `validate_module` does, and this crate does
    /// not depend on it), which is the hand-built/replayed-bundle threat model.
    #[test]
    fn a_terminator_that_is_not_the_last_instruction_declines() {
        let mut function = Function::new(FuncId::new(0), "clamp", FuncTyId::new(0), b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::U32));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(10),
            })
            .with_result(v(1)),
        );
        entry.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ugt,
                ty: Ty::U32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: v(2),
            then_target: b(1),
            then_args: vec![v(1)],
            else_target: b(1),
            else_args: vec![v(0)],
        }));
        // DEAD, and not the terminator: every real path leaves through the
        // `CondBr` above.
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        let mut join = Block::new(b(1));
        join.params.push((v(3), Ty::U32));
        join.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        function.blocks.extend([entry, join]);
        function.value_names = Some(vec![(v(0), "x".to_string())]);
        let module = module_with_functions(
            vec![function],
            vec![FuncTy {
                params: vec![Ty::U32],
                returns: vec![Ty::U32],
                is_vararg: false,
                abi: None,
            }],
        );
        let decline = lower(&module).expect_err("a terminator that is not last");
        assert!(decline.reason().contains("CondBr"), "{decline}");
        assert!(decline.reason().contains("TERMINATOR"), "{decline}");
    }
}
