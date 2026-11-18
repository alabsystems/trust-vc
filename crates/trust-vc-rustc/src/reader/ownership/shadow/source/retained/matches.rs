//! Original exhaustive enum matches with retained by-value arm bindings.
use super::*;

impl<'tcx> Retained<'_, 'tcx> {
    fn pattern(&mut self, pattern: &'tcx hir::Pat<'tcx>, depth: usize) -> Option<()> {
        self.charge(1)?;
        let source = &self.source;
        if depth > 64
            || pattern.hir_id.owner.def_id != source.definition
            || !pattern.default_binding_modes
            || !matches!(source.tcx.hir_node(pattern.hir_id), hir::Node::Pat(current) if std::ptr::eq(current, pattern))
            || source
                .typeck
                .pat_adjustments()
                .get(pattern.hir_id)
                .is_some_and(|row| !row.is_empty())
            || !attrs::verus_attrs_with_work(source.tcx.hir_attrs(pattern.hir_id), self.work)
                .ok()?
                .is_empty()
        {
            return None;
        }
        self.native_type(self.source.typeck.pat_ty(pattern), 0)?;
        match pattern.kind {
            hir::PatKind::Wild => Some(()),
            hir::PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) => {
                let source = &self.source;
                if !matches!(
                    source.typeck.pat_binding_modes().get(binding),
                    Some(BindingMode(ByRef::No, _))
                ) || source
                    .checked
                    .bindings
                    .mode_for(
                        source.tcx,
                        source.definition,
                        source.definition,
                        source.body,
                        pattern,
                    )
                    .ok()?
                    != Mode::Proof
                    || !self.bindings.insert(binding)
                    || !self.declared.insert(binding)
                {
                    return None;
                }
                Some(())
            }
            hir::PatKind::TupleStruct(ref path, parts, rest) => {
                if rest.as_opt_usize().is_some() {
                    return None;
                }
                let ty::Adt(adt, arguments) = self.source.typeck.pat_ty(pattern).kind() else {
                    return None;
                };
                if !adt.is_enum() {
                    return None;
                }
                let (_, variant) = datatypes::constructor_variant(
                    *adt,
                    self.source.typeck.qpath_res(path, pattern.hir_id),
                )?;
                if variant.fields.len() != parts.len() {
                    return None;
                }
                for (field, part) in variant.fields.iter().zip(parts) {
                    self.charge(1)?;
                    if self
                        .source
                        .tcx
                        .type_of(field.did)
                        .instantiate(self.source.tcx, arguments)
                        .skip_normalization()
                        != self.source.typeck.pat_ty(part)
                    {
                        return None;
                    }
                    self.pattern(part, depth + 1)?;
                }
                Some(())
            }
            hir::PatKind::Expr(value) => {
                let hir::PatExprKind::Path(ref path) = value.kind else {
                    return None;
                };
                let ty::Adt(adt, _) = self.source.typeck.pat_ty(pattern).kind() else {
                    return None;
                };
                if !adt.is_enum() {
                    return None;
                }
                let (_, variant) = datatypes::constructor_variant(
                    *adt,
                    self.source.typeck.qpath_res(path, value.hir_id),
                )?;
                variant.fields.is_empty().then_some(())
            }
            // Guards, reference/default-ref bindings, alternatives, rest and
            // record/tuple destructuring require their own retained proof.
            _ => None,
        }
    }

    pub(super) fn ordinary_match(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        scrutinee: &'tcx hir::Expr<'tcx>,
        arms: &'tcx [hir::Arm<'tcx>],
        depth: usize,
    ) -> Option<()> {
        self.charge(1)?;
        if depth > 128
            || arms.is_empty()
            || arms.len() > 1024
            || !matches!(self.source.typeck.expr_ty(scrutinee).kind(), ty::Adt(adt, _) if adt.is_enum())
        {
            return None;
        }
        // Guard census, exact native arm correspondence and this arm walk
        // all consume the same original transaction's allowance.
        self.charge(arms.len().checked_mul(3)?)?;
        if arms.iter().any(|arm| arm.guard.is_some()) {
            return None;
        }
        let source = &self.source;
        let facts = source
            .checked
            .matches
            .for_match(
                source.tcx,
                source.definition,
                source.definition,
                source.typeck,
                expression,
                scrutinee,
                arms,
            )
            .ok()?;
        if facts.scrutinee_mode != Mode::Proof
            || facts.result_mode != Mode::Proof
            || !self.matches.insert(expression.hir_id)
        {
            return None;
        }
        self.value(scrutinee, depth + 1)?;
        for arm in arms {
            self.charge(self.bindings.len().checked_add(1)?)?;
            let outer = self.bindings.clone();
            self.pattern(arm.pat, 0)?;
            self.value(arm.body, depth + 1)?;
            // Arm-local native identities never become available in another
            // arm. The immutable whole-body declaration roster is retained.
            self.bindings = outer;
        }
        self.nominal_operation = true;
        Some(())
    }
}
