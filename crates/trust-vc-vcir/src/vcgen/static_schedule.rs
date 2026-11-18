//! One actual dispatch per declaration/width. A private live plan retains the
//! actual source occurrences and completed backend results, never proof truth.

use super::*;
use crate::static_values::dependencies::{self, Flavor, Occurrence};
use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone, Copy)]
enum State {
    Checks,
    Spec,
    Trusted,
    Declared,
    Instance,
    Inlined,
    Refused,
}

impl State {
    fn actual(result: &FnVcs) -> Self {
        match result {
            FnVcs::Checks(_) => Self::Checks,
            FnVcs::Spec => Self::Spec,
            FnVcs::Trusted => Self::Trusted,
            FnVcs::Declared => Self::Declared,
            FnVcs::Instance => Self::Instance,
            FnVcs::Inlined => Self::Inlined,
            FnVcs::Refused(_) => Self::Refused,
        }
    }
}

struct Completed {
    entries: Vec<Option<State>>,
    groups: Vec<bool>,
    #[cfg(test)]
    dispatches: Vec<usize>,
}

struct Ready<'a> {
    occurrences: HashMap<FnId, Vec<Occurrence<'a>>>,
    ordinary: HashMap<FnId, BTreeSet<FnId>>,
    ordinary_components: Vec<Vec<FnId>>,
    indices: HashMap<FnId, usize>,
    component: HashMap<FnId, usize>,
    order: Vec<Vec<usize>>,
    cyclic_statics: HashSet<FnId>,
    completed: RefCell<Completed>,
}

/// Source references are covariant; the interior state contains no borrowed
/// source data. Moving the owning session does not change its Rc identity.
pub(super) struct Plan<'a> {
    source: &'a VcCrate,
    width: u32,
    policy: BitvectorPolicy,
    identity: Rc<()>,
    ready: Result<Ready<'a>, &'static str>,
}

fn charge(work: &Cell<usize>, amount: usize) -> Result<(), &'static str> {
    match work.get().checked_sub(amount) {
        Some(left) => {
            work.set(left);
            Ok(())
        }
        None => {
            work.set(0);
            Err("Static scheduling work exhausted")
        }
    }
}

fn build<'a>(source: &'a VcCrate, work: &Cell<usize>) -> Result<Ready<'a>, &'static str> {
    charge(work, source.fns.len().saturating_mul(6))?;
    let mut indices = HashMap::new();
    let mut occurrences = HashMap::new();
    let mut ordinary = HashMap::new();
    let mut extended = HashMap::new();
    for (index, owner) in source.fns.iter().enumerate() {
        if indices.insert(owner.id, index).is_some() {
            return Err("duplicate scheduling declaration identity");
        }
        let events = dependencies::occurrences(owner, work)?;
        let mut base = BTreeSet::new();
        let mut all = BTreeSet::new();
        for event in &events {
            charge(work, 2)?;
            if event.ordinary() {
                base.insert(event.target);
            }
            all.insert(event.target);
        }
        ordinary.insert(owner.id, base);
        extended.insert(owner.id, all);
        occurrences.insert(owner.id, events);
    }
    // Prepay both iterative SCC traversals and their node/edge inventories.
    // The ordinary graph is reused by the old uncovered-cycle rules below.
    for graph in [&ordinary, &extended] {
        for edges in graph.values() {
            charge(work, 8)?;
            charge(work, edges.len().saturating_mul(8))?;
        }
    }
    let ordinary_components = strongly_connected(&ordinary);
    // Prepay the existing ordinary diagnostic allocations, including joins
    // repeated for each refused component member. No extra SCC/source walk.
    for members in &ordinary_components {
        let cyclic = members.len() > 1
            || members
                .first()
                .is_some_and(|id| ordinary.get(id).is_some_and(|edges| edges.contains(id)));
        if !cyclic {
            continue;
        }
        let mut text = 0usize;
        for id in members {
            charge(work, 1)?;
            let length = indices
                .get(id)
                .map_or(1, |index| source.fns[*index].name.len());
            text = text.saturating_add(length.saturating_add(4));
        }
        charge(work, text.saturating_mul(members.len().saturating_add(2)))?;
        charge(work, members.len().saturating_mul(256))?;
    }
    let components = strongly_connected(&extended);
    charge(work, components.len())?;
    let mut component = HashMap::new();
    let mut order = Vec::new();
    let mut cyclic_statics = HashSet::new();
    for (position, members) in components.iter().enumerate() {
        charge(work, members.len().saturating_mul(4))?;
        let cyclic = members.len() > 1
            || members
                .first()
                .is_some_and(|id| extended.get(id).is_some_and(|edges| edges.contains(id)));
        let contains_static = members.iter().any(|id| {
            indices
                .get(id)
                .is_some_and(|index| source.fns[*index].kind == crate::FnKind::Static)
        });
        let mut actual = Vec::new();
        for id in members {
            component.insert(*id, position);
            if let Some(index) = indices.get(id) {
                actual.push(*index);
            }
            if cyclic && contains_static {
                cyclic_statics.insert(*id);
            }
        }
        let rounds = if actual.len() < 2 {
            0
        } else {
            (usize::BITS - (actual.len() - 1).leading_zeros()) as usize
        };
        charge(work, actual.len().saturating_mul(rounds).saturating_mul(2))?;
        actual.sort_unstable(); // source order within an ordinary recursive SCC
        order.push(actual);
    }
    // Tarjan emits dependency components first. Validate that contract before
    // any generation rather than silently relying on incidental iteration.
    for (owner, edges) in &extended {
        for target in edges {
            charge(work, 1)?;
            if component[target] > component[owner] {
                return Err("dependency condensation is not ordered");
            }
        }
    }
    charge(work, source.fns.len().saturating_add(order.len()))?;
    let completed = RefCell::new(Completed {
        entries: vec![None; source.fns.len()],
        groups: vec![false; order.len()],
        #[cfg(test)]
        dispatches: vec![0; source.fns.len()],
    });
    Ok(Ready {
        occurrences,
        ordinary,
        ordinary_components,
        indices,
        component,
        order,
        cyclic_statics,
        completed,
    })
}

impl<'a> Plan<'a> {
    fn new(ctx: &val::Ctx<'a>, source: &'a VcCrate) -> Self {
        let work = Cell::new(200_000); // one original planning account/width
        let ready = build(source, &work);
        Self {
            source,
            width: ctx.pointer_width,
            policy: ctx.bitvector_policy,
            identity: ctx.generation_identity.clone(),
            ready,
        }
    }

    pub(super) fn problem(&self) -> Option<&'static str> {
        self.ready.as_ref().err().copied()
    }

    fn matches(&self, ctx: &val::Ctx<'_>) -> bool {
        std::ptr::eq(self.source, ctx.source)
            && self.width == ctx.pointer_width
            && self.policy == ctx.bitvector_policy
            && Rc::ptr_eq(&self.identity, &ctx.generation_identity)
    }

    fn state(ready: &Ready<'_>, id: FnId) -> Result<State, &'static str> {
        let index = ready
            .indices
            .get(&id)
            .ok_or("an actual dependency result is missing")?;
        let component = ready
            .component
            .get(&id)
            .ok_or("an actual dependency component is missing")?;
        let completed = ready.completed.borrow();
        if !completed.groups[*component] {
            return Err("an actual dependency component is pending");
        }
        completed.entries[*index].ok_or("an actual dependency generation is pending")
    }

    pub(super) fn admit(
        &self,
        ctx: &val::Ctx<'_>,
        root: FnId,
        initializing: bool,
        work: &Cell<usize>,
    ) -> Result<(), &'static str> {
        if !self.matches(ctx) {
            return Err("a foreign source/context/width Static plan");
        }
        let ready = self.ready.as_ref().map_err(|problem| *problem)?;
        charge(work, 1)?;
        let mut pending = vec![root];
        let mut seen = HashSet::new();
        while let Some(id) = pending.pop() {
            charge(work, 1)?;
            if !seen.insert(id) {
                continue;
            }
            let declaration = ctx
                .fns
                .get(&id)
                .copied()
                .ok_or("an initializer dependency is missing")?;
            if ready.cyclic_statics.contains(&id) {
                return Err("a cycle through a Static initializer or contract");
            }
            if declaration.kind == crate::FnKind::Static && ctx.group(id).is_some() {
                return Err("a Static initializer belongs to a recursive group");
            }
            dependencies::declaration(declaration, &ctx.fns, &ctx.adts, work)?;
            if !(initializing && id == root) && matches!(Self::state(ready, id)?, State::Refused) {
                return Err("an actual initializer dependency generation was refused");
            }
            let events = ready
                .occurrences
                .get(&id)
                .ok_or("missing original dependency occurrences")?;
            for event in events {
                dependencies::validate(&ctx.fns, &ctx.adts, *event, work)?;
                if matches!(Self::state(ready, event.target)?, State::Inlined) {
                    charge(work, 1)?;
                    let owner = ctx
                        .checked_spec_original(event.owner.id)
                        .unwrap_or(event.owner);
                    if !matches!(event.flavor, Flavor::DecreasesBy)
                        || owner.decreases_by != Some(event.target)
                        || !matches!(Self::state(ready, owner.id)?, State::Checks)
                    {
                        return Err(
                            "an inline proof dependency lacks its completed termination owner",
                        );
                    }
                }
                charge(work, 1)?;
                pending.push(event.target);
            }
        }
        Ok(())
    }
}

pub(super) fn generate<'a>(
    ctx: &val::Ctx<'a>,
    tables: &spec::Tables,
    source: &'a VcCrate,
) -> (CrateVcs, Option<Plan<'a>>) {
    if !source
        .fns
        .iter()
        .any(|decl| decl.kind == crate::FnKind::Static)
    {
        let uncovered = uncovered_cycles(ctx, source);
        return (
            CrateVcs {
                fns: source
                    .fns
                    .iter()
                    .map(|decl| {
                        (
                            decl.id,
                            generate_declaration(ctx, tables, decl, &uncovered, None),
                        )
                    })
                    .collect(),
            },
            None,
        );
    }
    let plan = Plan::new(ctx, source);
    let ready = match &plan.ready {
        Ok(ready) => ready,
        Err(_) => {
            let uncovered = HashMap::new(); // no unchecked fallback traversal
            let fns = source
                .fns
                .iter()
                .map(|decl| {
                    (
                        decl.id,
                        generate_declaration(ctx, tables, decl, &uncovered, Some(&plan)),
                    )
                })
                .collect();
            return (CrateVcs { fns }, Some(plan));
        }
    };
    let uncovered = uncovered_cycles_components(ctx, &ready.ordinary, &ready.ordinary_components);
    let mut output = (0..source.fns.len())
        .map(|_| None)
        .collect::<Vec<Option<FnVcs>>>();
    for (component, members) in ready.order.iter().enumerate() {
        for index in members {
            let declaration = &source.fns[*index];
            let result = generate_declaration(ctx, tables, declaration, &uncovered, Some(&plan));
            {
                let mut completed = ready.completed.borrow_mut();
                completed.entries[*index] = Some(State::actual(&result));
                #[cfg(test)]
                {
                    completed.dispatches[*index] += 1;
                }
            }
            output[*index] = Some(result);
        }
        ready.completed.borrow_mut().groups[component] = true;
    }
    let fns = source
        .fns
        .iter()
        .zip(output)
        .map(|(decl, result)| {
            (
                decl.id,
                result.unwrap_or_else(|| {
                    FnVcs::Refused(val::refusal(
                        "static-schedule",
                        "missing actual declaration dispatch",
                        decl.span,
                    ))
                }),
            )
        })
        .collect();
    (CrateVcs { fns }, Some(plan))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DefHash, FnAttrs, FnKind, LocalDecl, LocalId, LocalKind, SiteId, SpanId, Ty};

    fn source() -> VcCrate {
        let ret = LocalId(0);
        let declaration = FnDecl {
            id: FnId(DefHash::new(0, 1)),
            name: "VALUE".into(),
            span: SpanId(0),
            mode: Mode::Exec,
            role: FnRole::Item,
            kind: FnKind::Static,
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
            ret,
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
        };
        let mut source = VcCrate::new("live_static");
        source.fns.push(declaration);
        source
    }

    #[test]
    fn private_plan_denies_pending_foreign_context_width_and_policy() {
        let source = source();
        let ctx = val::Ctx::new(&source);
        let pending = Plan::new(&ctx, &source);
        let id = source.fns[0].id;
        assert!(pending.admit(&ctx, id, false, &Cell::new(200_000)).is_err());
        assert!(pending.admit(&ctx, id, true, &Cell::new(200_000)).is_ok());
        let other = val::Ctx::new(&source);
        assert!(pending
            .admit(&other, id, true, &Cell::new(200_000))
            .is_err());
        let mut changed = val::Ctx::new(&source);
        let own = Plan::new(&changed, &source);
        changed.pointer_width = if changed.pointer_width == 32 { 64 } else { 32 };
        assert!(own.admit(&changed, id, true, &Cell::new(200_000)).is_err());
        let mut changed = val::Ctx::new(&source);
        let own = Plan::new(&changed, &source);
        changed.bitvector_policy = BitvectorPolicy::VerusSyntactic;
        assert!(own.admit(&changed, id, true, &Cell::new(200_000)).is_err());
        let cloned = source.clone();
        assert!(pending
            .admit(&val::Ctx::new(&cloned), id, true, &Cell::new(200_000))
            .is_err());
    }

    #[test]
    fn actual_dispatch_is_once_and_diagnostics_keep_the_same_completion_set() {
        let source = source();
        let session = GenerationSession::new(&source).unwrap();
        let (ctx, _, plan) = &session.widths[0];
        let plan = plan.as_ref().unwrap();
        let ready = plan.ready.as_ref().unwrap();
        assert_eq!(ready.completed.borrow().dispatches, vec![1]);
        assert!(plan
            .admit(ctx, source.fns[0].id, false, &Cell::new(200_000))
            .is_ok());
        let normal = session.vcs().clone();
        let _diagnostic = session.recommendations(source.fns[0].id).unwrap();
        assert_eq!(session.vcs(), &normal);
        assert_eq!(ready.completed.borrow().dispatches, vec![1]);
    }

    #[test]
    fn either_architecture_retains_two_actual_completion_contexts() {
        let mut source = source();
        source.architecture = crate::bitvector::Architecture::Either32Or64;
        let session = GenerationSession::new(&source).unwrap();
        assert_eq!(session.widths.len(), 2);
        let normal = session.vcs().clone();
        for (expected, (ctx, _, plan)) in [32, 64].into_iter().zip(&session.widths) {
            assert_eq!(ctx.pointer_width, expected);
            let plan = plan.as_ref().unwrap();
            let ready = plan.ready.as_ref().unwrap();
            assert_eq!(ready.completed.borrow().dispatches, vec![1]);
            assert!(matches!(
                Plan::state(ready, source.fns[0].id),
                Ok(State::Checks)
            ));
            assert!(plan
                .admit(ctx, source.fns[0].id, false, &Cell::new(200_000))
                .is_ok());
        }
        let (ctx32, _, plan32) = &session.widths[0];
        let (ctx64, _, plan64) = &session.widths[1];
        for (plan, foreign) in [
            (plan32.as_ref().unwrap(), ctx64),
            (plan64.as_ref().unwrap(), ctx32),
        ] {
            assert_eq!(
                plan.admit(foreign, source.fns[0].id, false, &Cell::new(200_000)),
                Err("a foreign source/context/width Static plan")
            );
        }
        session.recommendations(source.fns[0].id).unwrap();
        assert_eq!(session.vcs(), &normal);
        for (_, _, plan) in &session.widths {
            assert_eq!(
                plan.as_ref()
                    .unwrap()
                    .ready
                    .as_ref()
                    .unwrap()
                    .completed
                    .borrow()
                    .dispatches,
                vec![1]
            );
        }
    }

    #[test]
    fn an_actual_one_width_backend_refusal_blocks_its_static_and_merged_consumer() {
        let mut source = source();
        source.architecture = crate::bitvector::Architecture::Either32Or64;
        let mut helper = source.fns[0].clone();
        helper.id = FnId(DefHash::new(0, 2));
        helper.name = "helper".into();
        helper.kind = FnKind::Function;
        let mut consumer = helper.clone();
        consumer.id = FnId(DefHash::new(0, 3));
        consumer.name = "consumer".into();
        let mut local = source.fns[0].locals[0].clone();
        local.name = "destination".into();
        local.kind = LocalKind::Let;
        local.mutable = true;
        source.fns[0].locals.push(local.clone());
        consumer.locals.push(local);
        let bits = Expr::new(
            Ty::uint(32),
            SpanId(2),
            ExprKind::IntegerConstant(crate::IntegerConstant::Bits(crate::IntRange::USize)),
        );
        let condition = Expr::binary(
            crate::BinOp::Eq,
            bits,
            Expr::int_lit(64, Ty::uint(32), SpanId(2)),
            Ty::Bool,
            SpanId(2),
        );
        let call = |callee, site| {
            Stmt::new(
                SpanId(site),
                StmtKind::Call {
                    callee,
                    type_args: vec![],
                    args: vec![],
                    dest: Some(crate::Place::local(LocalId(1))),
                    site: SiteId(site),
                },
            )
        };
        let Body::Stmts(body) = &mut source.fns[0].body else {
            unreachable!()
        };
        // The destination has a valid local-table type but no StmtLet. Only
        // the real 64-bit branch executes that assignment and hard-refuses.
        body.stmts.insert(
            0,
            Stmt::new(
                SpanId(2),
                StmtKind::If {
                    cond: condition,
                    then_block: Block::new(vec![call(helper.id, 2)]),
                    else_block: Block::new(vec![]),
                },
            ),
        );
        consumer.body = Body::Stmts(Block::new(vec![
            Stmt::new(
                SpanId(3),
                StmtKind::Let {
                    local: LocalId(1),
                    init: None,
                },
            ),
            call(source.fns[0].id, 3),
            Stmt::new(
                SpanId(4),
                StmtKind::Return {
                    value: Some(Expr::read(
                        crate::Place::local(LocalId(1)),
                        Ty::uint(8),
                        SpanId(4),
                    )),
                    site: SiteId(4),
                },
            ),
        ]));
        // Deliberately place the consumer before both its dependencies.
        source.fns.insert(0, consumer);
        source.fns.push(helper);
        assert!(
            crate::check_crate(&source).is_empty(),
            "{:?}",
            crate::check_crate(&source)
        );
        let session = GenerationSession::new(&source).unwrap();
        let static_id = FnId(DefHash::new(0, 1));
        let consumer_id = FnId(DefHash::new(0, 3));
        for (width, (ctx, _, plan)) in [32, 64].into_iter().zip(&session.widths) {
            assert_eq!(ctx.pointer_width, width);
            let ready = plan.as_ref().unwrap().ready.as_ref().unwrap();
            assert_eq!(ready.completed.borrow().dispatches, vec![1, 1, 1]);
            for id in [static_id, consumer_id] {
                assert!(matches!(
                    (width, Plan::state(ready, id)),
                    (32, Ok(State::Checks)) | (64, Ok(State::Refused))
                ));
            }
        }
        let Some(FnVcs::Refused(initializer)) = session.vcs().get(static_id) else {
            panic!("{:?}", session.vcs());
        };
        assert_eq!(initializer.detail, "assignment to undeclared local");
        let Some(FnVcs::Refused(consumer)) = session.vcs().get(consumer_id) else {
            panic!("{:?}", session.vcs());
        };
        assert_eq!(consumer.tag, "static-read-dependency");
        assert!(consumer.detail.contains("generation was refused"));
        assert_eq!(
            session
                .vcs()
                .fns
                .iter()
                .map(|(id, _)| *id)
                .collect::<Vec<_>>(),
            source.fns.iter().map(|decl| decl.id).collect::<Vec<_>>()
        );
    }

    #[test]
    fn one_planning_account_depletes_without_a_fresh_retry_or_static_fallback() {
        let source = source();
        let work = Cell::new(200_000);
        assert!(build(&source, &work).is_ok());
        let spent = 200_000 - work.get();
        let exact = Cell::new(spent);
        assert!(build(&source, &exact).is_ok());
        assert_eq!(exact.get(), 0);
        assert!(build(&source, &exact).is_err());
        assert_eq!(exact.get(), 0);
        let short = Cell::new(spent - 1);
        assert!(build(&source, &short).is_err());
        assert_eq!(short.get(), 0);
    }
}
