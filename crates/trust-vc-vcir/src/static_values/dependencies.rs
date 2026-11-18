//! Bounded, occurrence-aware Static admission. No solver/proof-success cache.

use crate::{
    AdtDecl, AdtId, Block, Body, Expr, ExprKind, FnDecl, FnId, FnKind, FnRole, Mode, Stmt,
    StmtKind, Ty, VcCrate,
};
use std::cell::Cell;
use std::collections::{BTreeSet, HashMap};

type R<T> = Result<T, &'static str>;
const WORK: &str = "Static dependency work exhausted";

pub(super) fn charge(work: &Cell<usize>, amount: usize) -> R<()> {
    match work.get().checked_sub(amount) {
        Some(left) => {
            work.set(left);
            Ok(())
        }
        None => {
            work.set(0);
            Err(WORK)
        }
    }
}

enum Node<'a> {
    Expr(&'a Expr),
    Block(&'a Block, Mode),
    Stmt(&'a Stmt, Mode),
}

fn push<'a>(nodes: &mut Vec<Node<'a>>, node: Node<'a>, work: &Cell<usize>) -> R<()> {
    charge(work, 1)?;
    nodes.push(node);
    Ok(())
}

fn ty(adts: &HashMap<AdtId, &AdtDecl>, ty: &Ty, parameters: usize, work: &Cell<usize>) -> R<()> {
    // Static dependency admission has no associated-type declaration inventory.
    // It cannot manufacture that capability from an arbitrary type recipe.
    match crate::copy_context::wellformed_with(adts, &|_| None, ty, parameters, |n| charge(work, n))? {
        true => Ok(()),
        false => Err("an initializer dependency has an invalid type"),
    }
}

fn clause<'a>(nodes: &mut Vec<Node<'a>>, clause: &'a crate::Clause, work: &Cell<usize>) -> R<()> {
    for text in clause
        .attrs
        .proof_notes
        .iter()
        .chain(&clause.attrs.custom_errs)
    {
        charge(work, 1)?;
        charge(work, text.len())?;
    }
    push(nodes, Node::Expr(&clause.expr), work)
}

fn bare_dependency(functions: &HashMap<FnId, &FnDecl>, id: FnId, work: &Cell<usize>) -> R<()> {
    charge(work, 1)?;
    let target = functions
        .get(&id)
        .copied()
        .ok_or("an initializer/contract dependency is missing")?;
    // A declaration role alone is not an executable edge. Only the actual
    // typed Param-dispatch call below can use an abstract trait contract.
    if matches!(target.mode, Mode::Exec | Mode::Proof)
        && target.role == FnRole::TraitDecl
        && target.body == Body::None
        && !target.attrs.external_body
    {
        return Err("an abstract executable dependency has no represented dispatch occurrence");
    }
    Ok(())
}

fn static_shape(target: &FnDecl, adts: &HashMap<AdtId, &AdtDecl>, work: &Cell<usize>) -> R<()> {
    let valid = target.mode == Mode::Exec
        && target.role == FnRole::Item
        && target.type_params.is_empty()
        && target.params.is_empty()
        && target.copy_premises.is_empty()
        && target.requires.is_empty()
        && target.recommends.is_empty()
        && target.decreases.is_empty()
        && target.decreases_when.is_none()
        && target.decreases_by.is_none()
        && !target.attrs.inline
        && target.attrs.instance.is_none()
        && (matches!(target.body, Body::Stmts(_))
            || target.body == Body::None && target.attrs.external_body)
        && target
            .local(target.ret)
            .is_some_and(|ret| ret.mode == Mode::Exec && ret.kind == crate::LocalKind::Return);
    if !valid {
        return Err("an initializer dependency has an invalid Static declaration");
    }
    let result = target.ret_ty().ok_or("a Static dependency has no result")?;
    if !super::storage_type_budgeted(result, adts, work) {
        return Err("a Static dependency has unavailable stable storage");
    }
    Ok(())
}

fn call(
    owner: &FnDecl,
    target: &FnDecl,
    arguments: &[Ty],
    values: &[Expr],
    statement: bool,
    executed: bool,
    ambient: Mode,
    adts: &HashMap<AdtId, &AdtDecl>,
    work: &Cell<usize>,
) -> R<()> {
    charge(work, 1)?;
    if arguments.len() != target.type_params.len() || values.len() != target.params.len() {
        return Err("an initializer dependency call has the wrong arity");
    }
    for argument in arguments {
        ty(adts, argument, owner.type_params.len(), work)?;
    }
    for (value, param) in values.iter().zip(&target.params) {
        let formal = target
            .local(*param)
            .ok_or("an initializer dependency has no parameter")?;
        ty(adts, &value.ty, owner.type_params.len(), work)?;
        if !crate::copy_context::matches_substitution_with(&formal.ty, arguments, &value.ty, |n| {
            charge(work, n)
        })? {
            return Err("an initializer dependency call has an invalid argument type");
        }
    }
    if statement && executed {
        if target.kind == FnKind::Static {
            if ambient != Mode::Exec || !arguments.is_empty() || !values.is_empty() {
                return Err("an initializer dependency uses an invalid Static read");
            }
        } else if crate::executable_calls::representation(target, arguments, values.len()).is_some()
        {
            return Err(
                "an initializer dependency call is not represented by the executable backend",
            );
        }
        if ambient == Mode::Exec && target.mode == Mode::Proof
            || ambient == Mode::Proof && target.mode == Mode::Exec
        {
            return Err("an initializer dependency call has an invalid mode");
        }
    } else if !statement && target.mode != Mode::Spec {
        return Err("an initializer dependency expression calls a non-Spec declaration");
    }
    // Instance bodies are dependency data, not independently executed proofs.
    // Discharge the executed original body's actual call premises instead.
    if executed || !statement {
        for premise in &target.copy_premises {
            if !crate::copy_context::is_copy_with(
                adts,
                &owner.copy_premises,
                premise,
                Some(arguments),
                |n| charge(work, n),
            )? {
                return Err("an initializer dependency has an undischarged Copy premise");
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
pub(crate) enum Flavor<'a> {
    Statement {
        type_args: &'a [Ty],
        args: &'a [Expr],
        ambient: Mode,
    },
    Expression {
        type_args: &'a [Ty],
        args: &'a [Expr],
    },
    Broadcast,
    DecreasesBy,
    Origin,
    Reveal,
}

#[derive(Clone, Copy)]
pub(crate) struct Occurrence<'a> {
    pub(crate) owner: &'a FnDecl,
    pub(crate) target: FnId,
    pub(crate) flavor: Flavor<'a>,
}

impl Occurrence<'_> {
    pub(crate) fn ordinary(&self) -> bool {
        !matches!(self.flavor, Flavor::Origin | Flavor::Reveal)
    }
}

pub(crate) fn validate(
    functions: &HashMap<FnId, &FnDecl>,
    adts: &HashMap<AdtId, &AdtDecl>,
    occurrence: Occurrence<'_>,
    work: &Cell<usize>,
) -> R<()> {
    charge(work, 1)?;
    let owner = functions
        .get(&occurrence.owner.id)
        .copied()
        .ok_or("missing occurrence owner")?;
    if !std::ptr::eq(owner, occurrence.owner) {
        return Err("dependency occurrence belongs to another source");
    }
    let target = functions
        .get(&occurrence.target)
        .copied()
        .ok_or("an initializer/contract dependency is missing")?;
    let executed = owner.role != FnRole::Instance;
    match occurrence.flavor {
        Flavor::Statement {
            type_args,
            args,
            ambient,
        } => call(
            owner, target, type_args, args, true, executed, ambient, adts, work,
        ),
        Flavor::Expression { type_args, args } => call(
            owner,
            target,
            type_args,
            args,
            false,
            executed,
            Mode::Spec,
            adts,
            work,
        ),
        Flavor::Broadcast | Flavor::DecreasesBy => bare_dependency(functions, target.id, work),
        Flavor::Origin => Ok(()),
        Flavor::Reveal => {
            if target.role == FnRole::Imported || target.mode != Mode::Spec {
                Err("an initializer dependency reveals an unavailable Spec body")
            } else {
                Ok(())
            }
        }
    }
}

pub(crate) fn declaration(
    owner: &FnDecl,
    functions: &HashMap<FnId, &FnDecl>,
    adts: &HashMap<AdtId, &AdtDecl>,
    work: &Cell<usize>,
) -> R<()> {
    for local in &owner.locals {
        charge(work, 1)?;
        ty(adts, &local.ty, owner.type_params.len(), work)?;
    }
    for premise in &owner.copy_premises {
        ty(adts, premise, owner.type_params.len(), work)?;
    }
    if owner.kind == FnKind::Static {
        static_shape(owner, adts, work)?;
    }
    if owner.role == FnRole::Instance {
        if matches!(owner.mode, Mode::Exec | Mode::Proof)
            && !crate::instance_semantics::exec_contract_matches(functions, adts, owner, work)
        {
            return Err("an executable initializer instance lacks a checked substituted contract");
        }
        if owner.attrs.instance.is_none() {
            return Err("an initializer instance has no native origin");
        }
    } else if matches!(owner.mode, Mode::Exec | Mode::Proof)
        && owner.body == Body::None
        && !owner.attrs.external_body
        && owner.role != FnRole::TraitDecl
    {
        return Err(
            "an executable initializer dependency has no checked or explicitly trusted body",
        );
    }
    Ok(())
}

fn edges(
    functions: &HashMap<FnId, &FnDecl>,
    adts: &HashMap<AdtId, &AdtDecl>,
    owner: &FnDecl,
    work: &Cell<usize>,
) -> R<BTreeSet<FnId>> {
    let mut result = BTreeSet::new();
    for occurrence in occurrences(owner, work)? {
        validate(functions, adts, occurrence, work)?;
        charge(work, 1)?;
        result.insert(occurrence.target);
    }
    Ok(result)
}

pub(crate) fn occurrences<'a>(owner: &'a FnDecl, work: &Cell<usize>) -> R<Vec<Occurrence<'a>>> {
    charge(work, 1)?;
    let mut edges = Vec::new();
    let mut nodes = Vec::new();
    for clause_ in owner
        .requires
        .iter()
        .chain(&owner.ensures)
        .chain(&owner.recommends)
    {
        clause(&mut nodes, clause_, work)?;
    }
    for expression in owner.decreases.iter().chain(&owner.decreases_when) {
        push(&mut nodes, Node::Expr(expression), work)?;
    }
    if let Some(condition) = owner.unwind_spec().condition() {
        push(&mut nodes, Node::Expr(condition), work)?;
    }
    if let Some(groups) = &owner.attrs.broadcast_triggers {
        charge(work, groups.len())?;
        for group in groups {
            charge(work, group.len())?;
            for expression in group {
                push(&mut nodes, Node::Expr(expression), work)?;
            }
        }
    }
    if let Some(target) = owner.decreases_by {
        charge(work, 1)?;
        edges.push(Occurrence {
            owner,
            target,
            flavor: Flavor::DecreasesBy,
        });
    }
    if let Some(origin) = &owner.attrs.instance {
        charge(work, 1)?;
        edges.push(Occurrence {
            owner,
            target: origin.declaration,
            flavor: Flavor::Origin,
        });
    }
    match &owner.body {
        Body::Stmts(block) => push(&mut nodes, Node::Block(block, owner.mode), work)?,
        Body::Spec(expression) | Body::Constant(expression) => {
            push(&mut nodes, Node::Expr(expression), work)?
        }
        Body::None => {}
    }
    while let Some(node) = nodes.pop() {
        charge(work, 1)?;
        match node {
            Node::Expr(expression) => {
                if let ExprKind::Call {
                    callee,
                    type_args,
                    args,
                } = &expression.kind
                {
                    charge(work, 1)?;
                    edges.push(Occurrence {
                        owner,
                        target: *callee,
                        flavor: Flavor::Expression { type_args, args },
                    });
                }
                if let ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } =
                    &expression.kind
                {
                    push(&mut nodes, Node::Block(block, Mode::Proof), work)?;
                }
                super::child_work(expression, |n| charge(work, n))?;
                expression.for_each_child(&mut |child| nodes.push(Node::Expr(child)));
            }
            Node::Block(block, ambient) => {
                charge(work, block.stmts.len())?;
                nodes.extend(block.stmts.iter().map(|stmt| Node::Stmt(stmt, ambient)));
            }
            Node::Stmt(stmt, ambient) => match &stmt.kind {
                StmtKind::Call {
                    callee,
                    type_args,
                    args,
                    ..
                } => {
                    charge(work, 1)?;
                    edges.push(Occurrence {
                        owner,
                        target: *callee,
                        flavor: Flavor::Statement {
                            type_args,
                            args,
                            ambient,
                        },
                    });
                    for arg in args {
                        push(&mut nodes, Node::Expr(arg), work)?;
                    }
                }
                StmtKind::BroadcastUse { callee } => {
                    charge(work, 1)?;
                    edges.push(Occurrence {
                        owner,
                        target: *callee,
                        flavor: Flavor::Broadcast,
                    });
                }
                StmtKind::Reveal { callee, .. } | StmtKind::Hide { callee } => {
                    charge(work, 1)?;
                    edges.push(Occurrence {
                        owner,
                        target: *callee,
                        flavor: Flavor::Reveal,
                    });
                }
                StmtKind::Let { init, .. } => {
                    if let Some(expr) = init {
                        push(&mut nodes, Node::Expr(expr), work)?;
                    }
                }
                StmtKind::LetChecked { init, .. } => {
                    push(&mut nodes, Node::Expr(init), work)?;
                }
                StmtKind::Assign { value, .. } | StmtKind::AssignSpec { value, .. } => {
                    push(&mut nodes, Node::Expr(value), work)?
                }
                StmtKind::Assert { expr, .. } | StmtKind::Assume { expr, .. } => {
                    push(&mut nodes, Node::Expr(expr), work)?
                }
                StmtKind::AssertBitVector {
                    requires, ensures, ..
                } => {
                    for c in requires.iter().chain(ensures) {
                        clause(&mut nodes, c, work)?;
                    }
                }
                StmtKind::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    push(&mut nodes, Node::Expr(cond), work)?;
                    push(&mut nodes, Node::Block(then_block, ambient), work)?;
                    push(&mut nodes, Node::Block(else_block, ambient), work)?;
                }
                StmtKind::IfSpec {
                    cond,
                    then_block,
                    else_block,
                } => {
                    push(&mut nodes, Node::Expr(cond), work)?;
                    push(&mut nodes, Node::Block(then_block, Mode::Proof), work)?;
                    push(&mut nodes, Node::Block(else_block, Mode::Proof), work)?;
                }
                StmtKind::Return { value, .. } => {
                    if let Some(expr) = value {
                        push(&mut nodes, Node::Expr(expr), work)?;
                    }
                }
                StmtKind::Ghost(block) => push(&mut nodes, Node::Block(block, Mode::Proof), work)?,
                StmtKind::GhostTail { block, tail } => {
                    push(&mut nodes, Node::Block(block, Mode::Proof), work)?;
                    push(&mut nodes, Node::Expr(tail), work)?;
                }
                StmtKind::Block(block) => push(&mut nodes, Node::Block(block, ambient), work)?,
                StmtKind::Loop(lp) => {
                    if let Some(cond) = &lp.cond {
                        push(&mut nodes, Node::Block(&cond.block, ambient), work)?;
                        push(&mut nodes, Node::Expr(&cond.expr), work)?;
                    }
                    for invariant in &lp.invariants {
                        push(&mut nodes, Node::Expr(&invariant.expr), work)?;
                    }
                    for expression in &lp.decreases {
                        push(&mut nodes, Node::Expr(expression), work)?;
                    }
                    push(&mut nodes, Node::Block(&lp.body, ambient), work)?;
                }
                StmtKind::BorrowMut { .. }
                | StmtKind::Break { .. }
                | StmtKind::Continue { .. }
                | StmtKind::Unreachable => {}
            },
        }
    }
    Ok(edges)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DefHash, FnAttrs, LocalDecl, LocalId, LocalKind, SiteId, SpanId};

    fn declaration(id: u64, kind: FnKind) -> FnDecl {
        FnDecl {
            id: FnId(DefHash::new(0, id)),
            name: format!("value{id}"),
            span: SpanId(0),
            mode: Mode::Exec,
            role: FnRole::Item,
            kind,
            type_params: vec![],
            copy_premises: vec![],
            locals: vec![LocalDecl {
                name: "ret".into(),
                ty: Ty::uint(8),
                mode: Mode::Exec,
                prophecy: Default::default(),
                mutable: false,
                kind: LocalKind::Return,
                span: SpanId(0),
            }],
            params: vec![],
            ret: LocalId(0),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            decreases_when: None,
            decreases_by: None,
            unwind: None,
            attrs: FnAttrs::default(),
            body: Body::Stmts(Block::new(vec![Stmt::new(
                SpanId(1),
                StmtKind::Return {
                    value: Some(Expr::int_lit(3, Ty::uint(8), SpanId(1))),
                    site: SiteId(1),
                },
            )])),
        }
    }

    fn check_with(source: &VcCrate, work: &Cell<usize>) -> R<()> {
        let functions = source.fns.iter().map(|decl| (decl.id, decl)).collect();
        let adts = source.adts.iter().map(|decl| (decl.id, decl)).collect();
        check(source, &functions, &adts, source.fns[0].id, work)
    }

    #[test]
    fn original_allowance_depletes_across_repeated_reads_and_failure() {
        let mut source = VcCrate::new("budget");
        source.fns.push(declaration(1, FnKind::Static));
        let measure = Cell::new(100_000);
        assert_eq!(check_with(&source, &measure), Ok(()));
        let spent = 100_000 - measure.get();
        assert!(spent > 1);
        let zero = Cell::new(0);
        assert!(check_with(&source, &zero).is_err());
        assert_eq!(zero.get(), 0);
        let exact = Cell::new(spent);
        assert_eq!(check_with(&source, &exact), Ok(()));
        assert_eq!(exact.get(), 0);
        assert!(check_with(&source, &exact).is_err());
        assert_eq!(exact.get(), 0);
        let repeated = Cell::new(spent * 2 - 1);
        assert_eq!(check_with(&source, &repeated), Ok(()));
        assert!(check_with(&source, &repeated).is_err());
        assert_eq!(repeated.get(), 0);
        assert!(check_with(&source, &repeated).is_err());
        assert_eq!(repeated.get(), 0);
    }

    #[test]
    fn unreachable_and_nested_contract_dependencies_keep_the_same_work_and_denial() {
        let mut source = VcCrate::new("unreachable");
        let mut root = declaration(1, FnKind::Static);
        let mut dependency = declaration(2, FnKind::Function);
        dependency.role = FnRole::TraitDecl;
        dependency.type_params = vec!["Self".into()];
        dependency.body = Body::None;
        let Body::Stmts(body) = &mut root.body else {
            unreachable!()
        };
        body.stmts.push(Stmt::new(
            SpanId(2),
            StmtKind::Call {
                callee: dependency.id,
                type_args: vec![Ty::uint(8)],
                args: vec![],
                dest: None,
                site: SiteId(2),
            },
        ));
        source.fns = vec![root, dependency];
        let work = Cell::new(100_000);
        assert_eq!(
            check_with(&source, &work),
            Err("an initializer dependency call is not represented by the executable backend")
        );
        assert!(work.get() < 100_000);
        let remaining = work.get();
        assert!(check_with(&source, &work).is_err());
        assert!(work.get() < remaining);
        let declaration = &mut source.fns[0];
        let Body::Stmts(body) = &mut declaration.body else {
            unreachable!()
        };
        let hidden = body.stmts.pop().unwrap();
        declaration.ensures.push(crate::Clause {
            expr: Expr::new(
                Ty::Unit,
                SpanId(3),
                ExprKind::ProofInSpec(Block::new(vec![hidden])),
            ),
            span: SpanId(3),
            attrs: Default::default(),
        });
        assert!(check_with(&source, &work).is_err());
    }

    #[test]
    fn large_contract_and_diamond_do_not_receive_per_edge_grants() {
        let mut source = VcCrate::new("diamond");
        let mut root = declaration(1, FnKind::Static);
        let left = declaration(2, FnKind::Function);
        let right = declaration(3, FnKind::Function);
        let leaf = declaration(4, FnKind::Function);
        fn add_call(declaration: &mut FnDecl, id: FnId, site: u32) {
            let Body::Stmts(body) = &mut declaration.body else {
                unreachable!()
            };
            body.stmts.insert(
                0,
                Stmt::new(
                    SpanId(site),
                    StmtKind::Call {
                        callee: id,
                        type_args: vec![],
                        args: vec![],
                        dest: None,
                        site: SiteId(site),
                    },
                ),
            );
        }
        add_call(&mut root, left.id, 2);
        add_call(&mut root, right.id, 3);
        let mut left = left;
        let mut right = right;
        add_call(&mut left, leaf.id, 2);
        add_call(&mut right, leaf.id, 2);
        source.fns = vec![root, left, right, leaf];
        let measure = Cell::new(100_000);
        assert_eq!(check_with(&source, &measure), Ok(()));
        let spent = 100_000 - measure.get();
        let short = Cell::new(spent - 1);
        assert!(check_with(&source, &short).is_err());
        assert_eq!(short.get(), 0);
        for _ in 0..100 {
            source.fns[3].ensures.push(crate::Clause {
                expr: Expr::bool_lit(true, SpanId(0)),
                span: SpanId(0),
                attrs: Default::default(),
            });
        }
        let original = Cell::new(spent);
        assert!(check_with(&source, &original).is_err());
        assert_eq!(original.get(), 0);
    }
}

/// Validate a single reachable closure using the caller's existing allowance.
/// A result cannot be reused in another immutable source context.
pub(super) fn check(
    source: &VcCrate,
    functions: &HashMap<FnId, &FnDecl>,
    adts: &HashMap<AdtId, &AdtDecl>,
    root: FnId,
    work: &Cell<usize>,
) -> R<()> {
    charge(work, 1)?;
    let mut graph = HashMap::new();
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        charge(work, 1)?;
        if graph.contains_key(&id) {
            continue;
        }
        let owner = functions
            .get(&id)
            .copied()
            .ok_or("an initializer/contract dependency is missing")?;
        declaration(owner, functions, adts, work)?;
        let next = edges(functions, adts, owner, work)?;
        charge(work, next.len())?;
        pending.extend(next.iter().copied());
        graph.insert(id, next);
    }
    let mut groups = HashMap::new();
    for (index, group) in source.rec_groups.iter().enumerate() {
        charge(work, 1)?;
        for (member, _) in &group.members {
            charge(work, 1)?;
            if functions
                .get(member)
                .is_some_and(|decl| decl.kind == FnKind::Static)
                && graph.contains_key(member)
            {
                return Err("a Static initializer belongs to a recursive group");
            }
            if groups.insert(*member, index).is_some() {
                return Err("duplicate recursive dependency membership");
            }
        }
    }
    // Prepay the existing iterative SCC walk and its bounded per-node/edge
    // inventories. No recursive AST walk or fresh per-component allowance.
    for edges in graph.values() {
        charge(work, 8)?;
        charge(work, edges.len().saturating_mul(8))?;
    }
    for component in crate::vcgen::strongly_connected(&graph) {
        charge(work, component.len())?;
        let Some(first) = component.first() else {
            continue;
        };
        let cyclic =
            component.len() > 1 || graph.get(first).is_some_and(|edges| edges.contains(first));
        if !cyclic {
            continue;
        }
        if component
            .iter()
            .any(|id| functions[id].kind == FnKind::Static)
        {
            return Err("a cycle through a Static initializer or contract");
        }
        // Ordinary recursion is decided by actual backend generation. The
        // scheduler preserves its existing uncovered-cycle graph/rules; an
        // unexecuted instance body does not invent another recursion policy.
    }
    Ok(())
}
