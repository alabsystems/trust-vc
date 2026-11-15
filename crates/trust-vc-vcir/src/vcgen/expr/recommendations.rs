//! Auxiliary pure-expression checks; no normal proof or definition premises.

use super::*;

impl Tr<'_> {
    /// Verus checks cond and result under arbitrary typed choice binders,
    /// then checks a separate existential condition. It does not assume that
    /// condition while checking the result's own Spec-call domains.
    pub(super) fn choice_recommendations(
        &mut self,
        expression: &Expr,
        vars: &[(LocalId, Ty)],
        triggers: &[Vec<Expr>],
        condition: &Expr,
        result: &Expr,
    ) -> R<()> {
        let depth = self.bound.len();
        let diagnostic_depth = self.recommendation_symbols.len();
        let translated = self.bind(vars, expression.span).and_then(|leaves| {
            super::super::inline_work::items(&self.inline_work, leaves.len(), expression.span)?;
            self.recommendation_symbols.extend(leaves.iter().cloned());
            let condition = self.bool(condition)?;
            self.expr(result)?;
            // Actual hints are translated while these very bound leaves are
            // still live. Like upstream pure hint elaboration, they produce
            // neither domain checks nor physical proof events. Only the flags
            // and recorder are scoped away; auxiliary work keeps its SAME Cell.
            let recommendations = std::mem::replace(&mut self.recommendations, false);
            let events = self.rec_calls.take();
            let hints = self.quant_trigger_terms(triggers, &leaves, expression.span);
            self.rec_calls = events;
            self.recommendations = recommendations;
            Ok((leaves, condition, hints?))
        });
        self.bound.truncate(depth);
        self.recommendation_symbols.truncate(diagnostic_depth);
        let (leaves, predicate, hints) = translated?;
        // The original choice's ordinary template checks still run below,
        // including the existing concrete-domain/type/trigger admissions.
        let bound = leaves
            .iter()
            .map(|(name, leaf)| (name.clone(), leaf.sort()))
            .collect::<Vec<_>>();
        let facts = leaves
            .iter()
            .map(|(name, leaf)| leaf.fact(&Term::var(name.clone(), leaf.sort())));
        let body = Term::and(facts.chain([predicate]));
        super::super::inline_work::term(&self.inline_work, &body, 2, expression.span)?;
        // The registry retains normalized copies, as for ordinary quantified
        // auxiliary expressions. Admit their actual terms before those copies.
        for hint in hints.iter().flatten() {
            super::super::inline_work::term(&self.inline_work, hint.term(), 2, expression.span)?;
        }
        let goal = self
            .ctx
            .quants
            .borrow_mut()
            .quant(QuantKind::Exists, &bound, body, hints)
            .ok_or_else(|| {
                refusal(
                    "recommends-choice",
                    "an ill-sorted actual choose domain",
                    expression.span,
                )
            })?;
        self.pending(
            PendingKind::ChoiceRecommendation,
            goal,
            SiteId(condition.span.0),
            condition.span,
        )
    }
}
