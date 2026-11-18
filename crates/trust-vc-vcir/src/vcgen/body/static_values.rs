//! Stable global reads: no initializer equation or owned result transfer.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
use super::*;

impl Gen<'_> {
    pub(super) fn read_static(
        &mut self,
        path: &mut Path,
        target: &FnDecl,
        type_args: &[Ty],
        args: &[Expr],
        dest: Option<&Place>,
        span: SpanId,
    ) -> R<()> {
        let plan = self.static_plan.ok_or_else(|| {
            refusal(
                "static-schedule",
                "Static read has no live generation plan",
                span,
            )
        })?;
        plan.admit(self.ctx, target.id, false, &self.static_work)
            .map_err(|problem| refusal("static-read-dependency", problem, span))?;
        let ty = target
            .ret_ty()
            .ok_or_else(|| refusal("static-read", "missing static result", span))?;
        if target.kind != crate::FnKind::Static
            || target.mode != Mode::Exec
            || self.decl.mode != Mode::Exec
            || self.ghost_depth != 0
            || target.role != crate::FnRole::Item
            || !target.type_params.is_empty()
            || !target.params.is_empty()
            || !target.copy_premises.is_empty()
            || !type_args.is_empty()
            || !args.is_empty()
            || target
                .local(target.ret)
                .is_none_or(|local| local.mode != Mode::Exec)
            || !crate::static_values::storage_type_budgeted(ty, &self.ctx.adts, &self.static_work)
            || !target.requires.is_empty()
            || !target.recommends.is_empty()
            || self.ctx.group(target.id).is_some()
            || self.owner == target.id
        {
            return Err(refusal(
                "static-read",
                "invalid or cyclic stable-storage read",
                span,
            ));
        }
        super::super::call_identity::price_layout(self.ctx, ty, &self.static_work, span)?;
        let shape = self.ctx.shape_with_work(ty, None, span, &self.static_work)?;
        let result = match self.statics.get(&target.id) {
            Some(value) => {
                super::super::inline_work::value(&self.static_work, value, 2, span)?;
                value.clone()
            }
            None => {
                let value = self.fresh(&shape, &format!("static {}", target.name))?;
                super::super::inline_work::value(&self.static_work, &value, 2, span)?;
                self.statics.insert(target.id, value.clone());
                value
            }
        };
        // Loop isolation removes prior facts, but not the storage identity.
        // Re-establish only its genuine type membership, never its body.
        self.static_type_facts(&shape, &result, span)?;
        let reads = Reads {
            read: HashMap::from([(target.ret, result.clone())]),
            types: type_terms(self.ctx, target.id, &[], &self.types, span, &self.static_work)?,
            ..Reads::default()
        };
        for ensures in target
            .ensures
            .iter()
            .filter(|clause| !clause.attrs.is_labelled())
        {
            super::super::inline_work::expression(&self.static_work, &ensures.expr, span)?;
            let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads)
                .with_auxiliary_work(self.static_work.clone());
            let term = tr.bool(&ensures.expr)?;
            self.called_ok(&tr.called)?;
            if !tr.checks.is_empty() {
                return Err(refusal(
                    "static-read",
                    "a static contract contains executable checks",
                    span,
                ));
            }
            super::super::inline_work::items(&self.static_work, path.guard.len(), span)?;
            for guard in &path.guard {
                super::super::inline_work::term(&self.static_work, guard, 1, span)?;
            }
            self.fact(&path.guard, Source::CalleeEnsures, term);
        }
        if let Some(dest) = dest {
            self.assign(path, dest, result, span)?;
        }
        // No drop_identity_result, HasResolved, loan release or callee-owned
        // return summary is consumed on the static-read path.
        Ok(())
    }

    fn static_type_facts(&mut self, shape: &Shape, value: &Val, span: SpanId) -> R<()> {
        match (shape, value) {
            (Shape::Leaf(leaf), Val::Leaf(term)) => {
                let fact = self.ctx.type_fact_with_work(*leaf, &self.types, term, span, &self.static_work)?;
                self.fact(&[], Source::TypeFact, fact);
                Ok(())
            }
            (Shape::Node(shapes), Val::Node(values)) if shapes.len() == values.len() => {
                for (shape, value) in shapes.iter().zip(values) {
                    self.static_type_facts(shape, value, span)?;
                }
                Ok(())
            }
            _ => Err(refusal(
                "static-read",
                "static storage changed layout",
                span,
            )),
        }
    }
}
