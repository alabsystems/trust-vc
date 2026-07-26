//! Unit-type encoding helpers.
//!
//! Rust `()` has one inhabitant. The backend sort stays distinct from other
//! TrustVc sorts, and ground unit-typed terms are constrained to the shared unit
//! literal term.

use ay_dpll::api::{Solver, Term};

use crate::encoder::types::sort_for_type;
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcType;

pub(crate) const UNIT_TERM_NAME: &str = "__trust_vc_unit";

pub(crate) fn unit_term(solver: &mut Solver) -> Term {
    solver.declare_const(UNIT_TERM_NAME, sort_for_type(&TrustVcType::Unit))
}

pub(crate) fn unit_eq(solver: &mut Solver, term: Term) -> TrustVcResult<Term> {
    let unit = unit_term(solver);
    solver
        .try_eq(term, unit)
        .map_err(|e| TrustVcError::Encoding {
            context: "encode unit",
            detail: format!("Failed to build unit equality: {e}"),
        })
}

pub(crate) fn assert_unit_term(
    solver: &mut Solver,
    term: Term,
    context: &'static str,
    name: &str,
) -> TrustVcResult<()> {
    let eq = unit_eq(solver, term)?;
    solver
        .try_assert_term(eq)
        .map_err(|e| TrustVcError::Encoding {
            context,
            detail: format!("Failed to assert unit singleton constraint for '{name}': {e}"),
        })
}
