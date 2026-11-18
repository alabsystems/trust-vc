//! The existing statement-call representation boundary, shared with Static
//! dependency admission. This grants no body, native origin or proof verdict.

use crate::{FnDecl, FnRole, Mode, Ty};

pub(crate) enum Problem {
    Imported,
    Spec,
    Concrete,
    Mutable,
    Arity,
}

impl Problem {
    pub(crate) fn diagnostic(&self, target: &FnDecl) -> (&'static str, String) {
        match self {
            Self::Imported => (
                "imported-call",
                "an imported specification called as a statement".into(),
            ),
            Self::Spec => (
                "vcgen-internal",
                "a spec function called as a statement".into(),
            ),
            Self::Concrete => (
                "generic-clause",
                "a concrete generic contract without a native instance".into(),
            ),
            Self::Mutable => (
                "call-mut-ref",
                format!(
                    "a call of `{}`, which takes a `&mut` parameter",
                    target.name
                ),
            ),
            Self::Arity => ("vcgen-internal", "a call with the wrong arity".into()),
        }
    }
}

/// Static's separate kind-aware read path is checked by its own validator.
/// Keep these guards in the same order as ordinary Gen::call.
pub(crate) fn representation(target: &FnDecl, arguments: &[Ty], values: usize) -> Option<Problem> {
    if target.role == FnRole::Imported {
        return Some(Problem::Imported);
    }
    if target.mode == Mode::Spec {
        return Some(Problem::Spec);
    }
    // An unresolved associated constructor is abstract in the same way as a
    // caller parameter. WF still requires its exact registered declaration,
    // arity and every caller argument's scope; native bounds/selection remain
    // the producer's independent obligations. Closed constructors still need
    // a genuine concrete instance, exactly like other closed arguments.
    if arguments.iter().any(|ty| !matches!(ty, Ty::Param(_))
        && !(matches!(ty, Ty::Projection(..)) && ty.has_param())) {
        return Some(Problem::Concrete);
    }
    for id in &target.params {
        if target
            .local(*id)
            .is_some_and(|local| matches!(local.ty, Ty::Ref { mutable: true, .. }))
        {
            return Some(Problem::Mutable);
        }
    }
    (values != target.params.len()).then_some(Problem::Arity)
}
