//! Opaque reference operations through the crate's boxed value ABI.
use super::*;

impl Ctx<'_> {
    pub(crate) fn mut_ref_projection(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        reference: Val,
        future: bool,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        self.mut_ref_projection_with_work(ty, env, reference, future, span, None)
    }

    pub(crate) fn mut_ref_projection_with_work(
        &self, ty: &Ty, env: &TypeEnv, reference: Val, future: bool, span: SpanId,
        work: Option<&std::cell::Cell<usize>>,
    ) -> Result<Val, VcRefusal> {
        let Ty::MutRef(inner) = ty else {
            return Err(refusal(
                "mut-ref-type",
                "projection of a non-reference",
                span,
            ));
        };
        // Register the complete decorated referent identity before emitting
        // its projection's membership axioms.
        match work {
            Some(work) => self.type_argument_with_work(ty, env, span, work)?,
            None => self.type_argument(ty, env, span)?,
        };
        let Val::Leaf(reference) = reference else {
            return Err(refusal(
                "mut-ref-type",
                "a reference without opaque identity",
                span,
            ));
        };
        let value = self
            .types
            .borrow_mut()
            .mut_ref_projection(reference, future)
            .ok_or_else(|| {
                refusal(
                    "mut-ref-type",
                    "a reference projection with incompatible sort",
                    span,
                )
            })?;
        self.unbox_native_value_with_work(inner, env, value, span, work)
    }

    pub(crate) fn mut_ref_update(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        reference: Val,
        value: Val,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        self.mut_ref_update_with_work(ty, env, reference, value, span, None)
    }

    pub(crate) fn mut_ref_update_with_work(
        &self, ty: &Ty, env: &TypeEnv, reference: Val, value: Val, span: SpanId,
        work: Option<&std::cell::Cell<usize>>,
    ) -> Result<Val, VcRefusal> {
        let Ty::MutRef(inner) = ty else {
            return Err(refusal("mut-ref-type", "update of a non-reference", span));
        };
        match work {
            Some(work) => self.type_argument_with_work(ty, env, span, work)?,
            None => self.type_argument(ty, env, span)?,
        };
        let Val::Leaf(reference) = reference else {
            return Err(refusal(
                "mut-ref-type",
                "a reference without opaque identity",
                span,
            ));
        };
        let value = self.box_native_value_with_work(inner, env, value, span, work)?;
        self.types
            .borrow_mut()
            .mut_ref_update(reference, value)
            .map(Val::Leaf)
            .ok_or_else(|| {
                refusal(
                    "mut-ref-type",
                    "a reference update with incompatible sorts",
                    span,
                )
            })
    }

    pub(crate) fn has_resolved(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        value: Val,
        span: SpanId,
    ) -> Result<Term, VcRefusal> {
        self.has_resolved_inner(ty, env, value, span, None)
    }

    pub(crate) fn has_resolved_with_work(
        &self, ty: &Ty, env: &TypeEnv, value: Val, span: SpanId,
        work: &std::cell::Cell<usize>,
    ) -> Result<Term, VcRefusal> {
        self.has_resolved_inner(ty, env, value, span, Some(work))
    }

    fn has_resolved_inner(
        &self, ty: &Ty, env: &TypeEnv, value: Val, span: SpanId,
        work: Option<&std::cell::Cell<usize>>,
    ) -> Result<Term, VcRefusal> {
        let argument = match work {
            Some(work) => self.type_argument_with_work(ty, env, span, work)?,
            None => self.type_argument(ty, env, span)?,
        };
        let value = self.box_native_value_with_work(ty, env, value, span, work)?;
        let recipe = self.type_recipe(ty, env.owner(), span)?;
        if self.types.borrow().requires_projection_work(&recipe, env) || env.projection_work().is_some() {
            let work = env.projection_work().map(|work| work.as_ref()).or(work)
                .ok_or_else(|| refusal("resolution-type", "a projected resolution predicate has no caller work", span))?;
            for term in argument.terms_ref() { super::super::inline_work::term(work, term, 1, span)?; }
        }
        self.types
            .borrow_mut()
            .has_resolved(argument, value)
            .ok_or_else(|| {
                refusal(
                    "resolution-type",
                    "a resolution predicate with incompatible sort",
                    span,
                )
            })
    }
}
