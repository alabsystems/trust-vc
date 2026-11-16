//! Source-derived independent-query retention. This is a traversal index, not
//! model/read/import/body authority. It is built solely from the common SST
//! structural live-prefix BEFORE any ordinary architecture/path evaluation.
//! A return/Maybe::Never genuinely discards its suffix; an ordinary false path
//! does not discard an isolated question. No solver work or new work cap exists.

use super::*;
use std::collections::HashSet;
use std::marker::PhantomData;

#[derive(Clone, Copy, Default)]
struct Found {
    query: bool,
    needed: bool,
}

pub(super) struct Queries<'a> {
    needed: HashSet<*const Stmt>,
    expected: Vec<&'a Stmt>,
    expected_ids: HashSet<*const Stmt>,
    seen: HashSet<*const Stmt>,
    // Addresses are read only while the original immutable declaration is
    // borrowed. They are never dereferenced, published or reused as authority.
    source: PhantomData<&'a FnDecl>,
}
impl<'a> Queries<'a> {
    pub(super) fn capture(decl: &'a FnDecl) -> Self {
        let mut this = Self {
            needed: HashSet::new(),
            expected: vec![],
            expected_ids: HashSet::new(),
            seen: HashSet::new(),
            source: PhantomData,
        };
        this.extend(decl);
        this
    }
    pub(super) fn extend(&mut self, decl: &'a FnDecl) {
        match &decl.body {
            Body::Stmts(block) => {
                self.block(block, false);
            }
            Body::Spec(expr) | Body::Constant(expr) => {
                self.expr(expr, false);
            }
            Body::None => {}
        }
    }
    pub(super) fn needed(&self, stmt: &Stmt) -> bool {
        self.needed.contains(&(stmt as *const Stmt))
    }
    pub(super) fn emitted(&mut self, stmt: &'a Stmt) {
        self.seen.insert(stmt as *const Stmt);
    }
    pub(super) fn was_emitted(&self, stmt: &Stmt) -> bool {
        self.seen.contains(&(stmt as *const Stmt))
    }
    pub(super) fn finish(&self) -> R<()> {
        if let Some(stmt) = self
            .expected
            .iter()
            .find(|s| !self.seen.contains(&(**s as *const Stmt)))
        {
            return Err(refusal("architecture", "a required isolated BV source assertion was not generated in this ordinary context",stmt.span));
        }
        Ok(())
    }
    fn block(&mut self, block: &'a Block, continuation: bool) -> Found {
        let mut later = continuation;
        let mut out = Found::default();
        // Existing live_prefix is the source/SST Maybe::Never boundary. It
        // does not consult an ordinary width's facts, values or branch guard.
        for stmt in live_prefix(block).iter().rev() {
            let found = self.stmt(stmt, later);
            out.query |= found.query;
            out.needed |= found.needed;
            later |= found.query;
        }
        out
    }
    fn expr(&mut self, expr: &'a Expr, later: bool) -> Found {
        if let ExprKind::ProofInSpec(block) = &expr.kind {
            return self.block(block, later);
        }
        if let ExprKind::ProofInSpecTail { block, tail } = &expr.kind {
            return self.block_tail(block, tail, later);
        }
        let mut out = Found::default();
        expr.for_each_child(&mut |child| {
            let found = self.expr(child, later);
            out.query |= found.query;
            out.needed |= found.needed;
        });
        out
    }
    fn block_tail(&mut self, block: &'a Block, tail: &'a Expr, later: bool) -> Found {
        let tail = if block.stmts.iter().any(diverges) {
            Found::default()
        } else {
            self.expr(tail, later)
        };
        let prefix = self.block(block, later || tail.query);
        Found {
            query: prefix.query || tail.query,
            needed: prefix.needed || tail.needed,
        }
    }
    fn stmt(&mut self, stmt: &'a Stmt, later: bool) -> Found {
        let mut out = Found::default();
        match &stmt.kind {
            StmtKind::AssertBitVector { .. } => {
                if self.expected_ids.insert(stmt as *const Stmt) {
                    self.expected.push(stmt);
                }
                out.query = true;
                out.needed = true;
            }
            StmtKind::If {
                then_block,
                else_block,
                ..
            } => {
                let a = self.block(then_block, later);
                let b = self.block(else_block, later);
                out.query = a.query || b.query;
                out.needed = a.needed || b.needed;
            }
            StmtKind::Ghost(block) | StmtKind::Block(block) => {
                out = self.block(block, later);
            }
            StmtKind::GhostTail { block, tail } => {
                out = self.block_tail(block, tail, later);
            }
            StmtKind::Loop(lp) => {
                if let Some(cond) = &lp.cond {
                    let found = self.block(&cond.block, later);
                    out.query |= found.query;
                    out.needed |= found.needed;
                }
                let found = self.block(&lp.body, later);
                out.query |= found.query;
                out.needed |= found.needed;
            }
            _ => {}
        }
        // Retain the ordinary typed availability operations a later isolated
        // question may read. Their guard stays false; their SSA facts never
        // become isolated hypotheses. Existing mode/MIR/shape checks still run.
        out.needed |= later
            && matches!(
                &stmt.kind,
                StmtKind::Let { .. } | StmtKind::Assign { .. } | StmtKind::Call { .. }
            );
        if !matches!(stmt.kind, StmtKind::GhostTail { .. }) {
            for expr in super::super::stmt_exprs(stmt) {
                let found = self.expr(expr, later);
                out.query |= found.query;
                out.needed |= found.needed;
            }
        }
        if out.needed {
            self.needed.insert(stmt as *const Stmt);
        }
        out
    }
}
