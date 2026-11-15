// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Lowering of a checked v0 chain to trust-vc typed IR.
//!
//! Every scalar value becomes one bit-vector (or Bool) variable, and every
//! definition becomes a typed `Assume` equation `v == e`. Only these node
//! kinds are ever emitted: `WrappingArith { mode: Wrapping }`, `Cast`
//! (integer to integer), `Compare`, `Logic`, `Not`, `IntLit`, `BoolLit` and
//! `Var`. No `MathInt`/`Nat`/`Real` variable exists, so the encoder session
//! stays in bit-vector mode, and `TrustExpr` (whose default overflow behavior
//! is `Allow` and which has no wrapping node) is never involved.
//!
//! Names deliberately avoid every substring the encoder decodes from
//! obligation names (`__`, `calc_`, `loop_`, `post_loop`, `_step_`,
//! `requires`, `body_axiom`, `assertion_`, `assumption_`, `_dom`,
//! `_unreachable`, `overflow_check_`, `index_bounds_check_`).

use trust_vc_core::ir::{ArithOp, CompareOp, LogicOp, TrustVcExpr, TrustVcType, WrappingMode};
use trust_vc_core::vc::{
    Div0Behavior, OverflowBehavior, TypedProofObligation, VariableDecl, VerificationContext,
};

use trust_ir::{BlockId, ICmpOp, ValueId};

use super::check::{ArithKind, BoolKind, CheckedBody, DefExpr, ScalarTy, StepKind};

pub(crate) fn value_var_name(value: ValueId) -> String {
    format!("tirb_v{}", value.0)
}

pub(crate) fn def_name(value: ValueId) -> String {
    format!("tirb_def_v{}", value.0)
}

pub(crate) fn assume_name(block: BlockId, inst_index: u32) -> String {
    format!("tirb_asm_b{}_i{inst_index}", block.0)
}

pub(crate) fn site_name(block: BlockId, inst_index: u32) -> String {
    format!("tirb_site_b{}_i{inst_index}", block.0)
}

pub(crate) fn premises_name(block: BlockId, inst_index: u32) -> String {
    format!("tirb_premises_b{}_i{inst_index}", block.0)
}

pub(crate) const fn scalar_type(ty: ScalarTy) -> TrustVcType {
    match ty {
        ScalarTy::Bool => TrustVcType::Bool,
        ScalarTy::Int { bits, signed: true } => TrustVcType::Int { width: bits },
        ScalarTy::Int {
            bits,
            signed: false,
        } => TrustVcType::Uint { width: bits },
    }
}

/// One solver query: declarations, typed obligations, and the names the
/// certificate binding needs.
pub(crate) struct Query {
    pub(crate) variables: Vec<VariableDecl>,
    pub(crate) obligations: Vec<TypedProofObligation>,
    pub(crate) assertion_name: String,
    pub(crate) assumption_names: Vec<String>,
}

impl Query {
    /// Build the verification context with overflow and division behavior
    /// set EXPLICITLY. Wrapping is encoded structurally, so `Allow` only
    /// states that no checks are to be added on top of it.
    pub(crate) fn into_context(self) -> VerificationContext {
        let mut context = VerificationContext::from_typed_parts(self.variables, self.obligations);
        context.set_overflow_behavior(OverflowBehavior::Allow);
        context.set_div0_behavior(Div0Behavior::Allow);
        context
    }
}

fn var(body: &CheckedBody, value: ValueId) -> TrustVcExpr {
    // Every operand was checked to be a defined scalar before a step naming
    // it was emitted, so the lookup cannot miss; `Bool` is a harmless
    // fallback that would make the encoder refuse rather than mis-type.
    let ty = body
        .value_types
        .get(&value)
        .copied()
        .unwrap_or(ScalarTy::Bool);
    TrustVcExpr::Var {
        name: value_var_name(value),
        ty: scalar_type(ty),
    }
}

fn arith_op(op: ArithKind) -> ArithOp {
    match op {
        ArithKind::Add => ArithOp::Add,
        ArithKind::Sub => ArithOp::Sub,
        ArithKind::Mul => ArithOp::Mul,
    }
}

fn compare(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn cast(expr: TrustVcExpr, from_ty: TrustVcType, to_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Cast {
        expr: Box::new(expr),
        from_ty,
        to_ty,
    }
}

fn wrapping(op: ArithKind, left: TrustVcExpr, right: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::WrappingArith {
        mode: WrappingMode::Wrapping,
        op: arith_op(op),
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

/// The right-hand side of `value == expr`.
fn def_rhs(body: &CheckedBody, ty: ScalarTy, expr: &DefExpr) -> TrustVcExpr {
    match expr {
        DefExpr::IntConst(k) => TrustVcExpr::IntLit {
            value: *k,
            ty: scalar_type(ty),
        },
        DefExpr::BoolConst(b) => TrustVcExpr::BoolLit(*b),
        DefExpr::BoolBinary { op, lhs, rhs } => {
            // Both operands already denote evaluated, type-checked SSA values.
            // Core's short-circuit nodes cannot suppress any source instruction.
            let left = var(body, *lhs);
            let right = var(body, *rhs);
            match op {
                BoolKind::And => and(left, right),
                BoolKind::Or => TrustVcExpr::Logic {
                    op: LogicOp::Or,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                BoolKind::Xor => compare(CompareOp::Ne, left, right),
            }
        }
        DefExpr::Wrap { op, lhs, rhs } => {
            wrapping(*op, var(body, *lhs), var(body, *rhs), scalar_type(ty))
        }
        DefExpr::OverflowFlag {
            op,
            operand_ty,
            lhs,
            rhs,
        } => overflow_flag(body, *op, *operand_ty, *lhs, *rhs),
        DefExpr::ICmp {
            op,
            operand_ty,
            lhs,
            rhs,
        } => icmp(body, *op, *operand_ty, *lhs, *rhs),
        DefExpr::Alias(source) => var(body, *source),
    }
}

/// trust-ir's overflow flag (interpret.rs `signed_overflow` /
/// `unsigned_overflow`): the exact result of the operation lies outside
/// `[MIN_T, MAX_T]`. The exact result of add/sub/mul of two w-bit values is
/// representable at 2w bits, so compute it there with the extension the
/// operand TYPE dictates (sign for signed, zero for unsigned) and
/// range-check it. An unsigned negative difference wraps to at least
/// `2^(2w) - 2^w > MAX_T` and is flagged, exactly like `lhs < rhs`.
fn overflow_flag(
    body: &CheckedBody,
    op: ArithKind,
    operand_ty: ScalarTy,
    lhs: ValueId,
    rhs: ValueId,
) -> TrustVcExpr {
    let ScalarTy::Int { bits, signed } = operand_ty else {
        // `check_node` refuses Overflow on Bool before a step is emitted.
        return TrustVcExpr::BoolLit(true);
    };
    let (min, max) = operand_ty.int_bounds().unwrap_or((0, 0));
    let narrow = scalar_type(operand_ty);
    let wide = scalar_type(ScalarTy::Int {
        bits: bits * 2,
        signed,
    });
    let exact = wrapping(
        op,
        cast(var(body, lhs), narrow.clone(), wide.clone()),
        cast(var(body, rhs), narrow, wide.clone()),
        wide.clone(),
    );
    let in_range = and(
        compare(
            CompareOp::Ge,
            exact.clone(),
            TrustVcExpr::IntLit {
                value: min,
                ty: wide.clone(),
            },
        ),
        compare(
            CompareOp::Le,
            exact,
            TrustVcExpr::IntLit {
                value: max,
                ty: wide,
            },
        ),
    );
    TrustVcExpr::Not(Box::new(in_range))
}

/// `ICmp`: equality is signedness-free; an ordered compare takes its
/// signedness from the OP (interpret.rs `eval_int_icmp`), so operands whose
/// TYPE disagrees are reinterpreted at the same width first. The encoder's
/// BV compare reads signedness from the operand IR types.
fn icmp(
    body: &CheckedBody,
    op: ICmpOp,
    operand_ty: ScalarTy,
    lhs: ValueId,
    rhs: ValueId,
) -> TrustVcExpr {
    let (compare_op, op_signed) = match op {
        ICmpOp::Eq => return compare(CompareOp::Eq, var(body, lhs), var(body, rhs)),
        ICmpOp::Ne => return compare(CompareOp::Ne, var(body, lhs), var(body, rhs)),
        ICmpOp::Ult => (CompareOp::Lt, false),
        ICmpOp::Ule => (CompareOp::Le, false),
        ICmpOp::Ugt => (CompareOp::Gt, false),
        ICmpOp::Uge => (CompareOp::Ge, false),
        ICmpOp::Slt => (CompareOp::Lt, true),
        ICmpOp::Sle => (CompareOp::Le, true),
        ICmpOp::Sgt => (CompareOp::Gt, true),
        ICmpOp::Sge => (CompareOp::Ge, true),
    };
    let ScalarTy::Int { bits, signed } = operand_ty else {
        // `check_node` refuses ordered ICmp on Bool before a step is emitted.
        return TrustVcExpr::BoolLit(false);
    };
    let operand = |value| {
        let expr = var(body, value);
        if signed == op_signed {
            expr
        } else {
            cast(
                expr,
                scalar_type(operand_ty),
                scalar_type(ScalarTy::Int {
                    bits,
                    signed: op_signed,
                }),
            )
        }
    };
    compare(compare_op, operand(lhs), operand(rhs))
}

/// Declarations and definition equations for every step strictly before
/// `position` in chain order.
fn prefix(
    body: &CheckedBody,
    position: usize,
) -> (Vec<VariableDecl>, Vec<TypedProofObligation>, Vec<String>) {
    let mut variables = body
        .params
        .iter()
        .map(|(value, ty)| VariableDecl::new(value_var_name(*value), scalar_type(*ty)))
        .collect::<Vec<_>>();
    let mut obligations = Vec::new();
    let mut names = Vec::new();
    for step in body.steps.iter().filter(|step| step.position < position) {
        if let StepKind::Def { value, ty, expr } = &step.kind {
            variables.push(VariableDecl::new(value_var_name(*value), scalar_type(*ty)));
            let equation = compare(CompareOp::Eq, var(body, *value), def_rhs(body, *ty, expr));
            names.push(def_name(*value));
            obligations.push(TypedProofObligation::assume(def_name(*value), equation));
        }
    }
    (variables, obligations, names)
}

/// Premises of the site at `position`: the conditions of every `Assume`
/// strictly before it in chain order.
fn premises(body: &CheckedBody, position: usize) -> Vec<(String, ValueId)> {
    body.steps
        .iter()
        .filter(|step| step.position < position)
        .filter_map(|step| match step.kind {
            StepKind::Assume { cond } => Some((assume_name(step.block, step.inst_index), cond)),
            _ => None,
        })
        .collect()
}

/// The site query: `defs(< s) ∧ assumes(< s) → cond(s)`. Earlier `Assert`s
/// are NOT assumed, and nothing at or after the site is present.
pub(crate) fn site_query(
    body: &CheckedBody,
    position: usize,
    block: BlockId,
    inst_index: u32,
    cond: ValueId,
) -> Query {
    let (variables, mut obligations, mut assumption_names) = prefix(body, position);
    for (name, premise) in premises(body, position) {
        obligations.push(TypedProofObligation::assume(
            name.clone(),
            var(body, premise),
        ));
        assumption_names.push(name);
    }
    let assertion_name = site_name(block, inst_index);
    obligations.push(TypedProofObligation::assert(
        assertion_name.clone(),
        var(body, cond),
    ));
    Query {
        variables,
        obligations,
        assertion_name,
        assumption_names,
    }
}

/// The premise probe: definitions assumed, and the assertion
/// `!(p1 && … && pn)` (`false` when there are no premises). `Verified` means
/// the premises are unsatisfiable; a counterexample is a candidate witness.
pub(crate) fn premise_query(
    body: &CheckedBody,
    position: usize,
    block: BlockId,
    inst_index: u32,
) -> Query {
    let (variables, mut obligations, assumption_names) = prefix(body, position);
    let conjunction = premises(body, position)
        .into_iter()
        .map(|(_, premise)| var(body, premise))
        .reduce(and);
    let goal = match conjunction {
        Some(all) => TrustVcExpr::Not(Box::new(all)),
        None => TrustVcExpr::BoolLit(false),
    };
    let assertion_name = premises_name(block, inst_index);
    obligations.push(TypedProofObligation::assert(assertion_name.clone(), goal));
    Query {
        variables,
        obligations,
        assertion_name,
        assumption_names,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trust_ir_body::check::check_function;
    use trust_ir::{
        Block, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, OverflowOp,
        Ty,
    };

    /// Whitelist walker: fails on anything other than the node kinds and
    /// types this lane promises to emit.
    fn assert_bv_only(expr: &TrustVcExpr) {
        fn ty_ok(ty: &TrustVcType) {
            assert!(
                matches!(
                    ty,
                    TrustVcType::Bool | TrustVcType::Int { .. } | TrustVcType::Uint { .. }
                ),
                "non-BV type {ty:?} emitted"
            );
        }
        match expr {
            TrustVcExpr::BoolLit(_) => {}
            TrustVcExpr::IntLit { ty, .. } | TrustVcExpr::Var { ty, .. } => ty_ok(ty),
            TrustVcExpr::Compare { left, right, .. } | TrustVcExpr::Logic { left, right, .. } => {
                assert_bv_only(left);
                assert_bv_only(right);
            }
            TrustVcExpr::Not(inner) => assert_bv_only(inner),
            TrustVcExpr::Cast {
                expr,
                from_ty,
                to_ty,
            } => {
                assert!(
                    matches!(from_ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
                        && matches!(to_ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. }),
                    "non int-to-int cast {from_ty:?} -> {to_ty:?}"
                );
                assert_bv_only(expr);
            }
            TrustVcExpr::WrappingArith {
                mode,
                left,
                right,
                ty,
                ..
            } => {
                assert_eq!(*mode, WrappingMode::Wrapping, "non-wrapping arithmetic");
                ty_ok(ty);
                assert_bv_only(left);
                assert_bv_only(right);
            }
            other => panic!("forbidden node emitted: {other:?}"),
        }
    }

    fn node(inst: Inst, results: &[u32]) -> InstrNode {
        InstrNode::new(inst).with_results(results.iter().map(|r| ValueId::new(*r)))
    }

    /// Every instruction kind v0 admits, in one body.
    fn every_admitted_shape() -> Module {
        let v = ValueId::new;
        let mut module = Module::new("shape");
        module.func_types.push(FuncTy {
            params: vec![Ty::I8, Ty::U16],
            returns: vec![Ty::I8],
            is_vararg: false,
            abi: None,
        });
        let mut entry = Block::new(trust_ir::BlockId::new(0))
            .with_param(v(0), Ty::I8)
            .with_param(v(1), Ty::U16);
        entry.body = vec![
            node(
                Inst::Const {
                    ty: Ty::I8,
                    value: Constant::Int(-3),
                },
                &[2],
            ),
            node(
                Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I8,
                    lhs: v(0),
                    rhs: v(2),
                },
                &[3],
            ),
            node(Inst::Assume { cond: v(3) }, &[]),
            node(
                Inst::Overflow {
                    op: OverflowOp::MulOverflow,
                    ty: Ty::I8,
                    lhs: v(0),
                    rhs: v(2),
                },
                &[4, 5],
            ),
            node(
                Inst::Undef {
                    ty: Ty::Tuple(vec![Ty::I8, Ty::Bool]),
                },
                &[6],
            ),
            node(
                Inst::InsertField {
                    ty: Ty::Tuple(vec![Ty::I8, Ty::Bool]),
                    aggregate: v(6),
                    field: 0,
                    value: v(4),
                },
                &[7],
            ),
            node(
                Inst::InsertField {
                    ty: Ty::Tuple(vec![Ty::I8, Ty::Bool]),
                    aggregate: v(7),
                    field: 1,
                    value: v(5),
                },
                &[8],
            ),
            node(
                Inst::ExtractField {
                    ty: Ty::Bool,
                    aggregate: v(8),
                    field: 1,
                },
                &[9],
            ),
            node(
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                },
                &[10],
            ),
            node(
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::Bool,
                    lhs: v(9),
                    rhs: v(10),
                },
                &[11],
            ),
            node(
                Inst::Assert {
                    cond: v(11),
                    kind: Default::default(),
                    site: None,
                },
                &[],
            ),
            node(
                Inst::BinOp {
                    op: trust_ir::BinOp::Sub,
                    ty: Ty::U16,
                    lhs: v(1),
                    rhs: v(1),
                },
                &[12],
            ),
            node(
                Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::U16,
                    lhs: v(12),
                    rhs: v(1),
                },
                &[13],
            ),
            node(
                Inst::Copy {
                    ty: Ty::Bool,
                    operand: v(13),
                },
                &[14],
            ),
            node(
                Inst::Br {
                    target: trust_ir::BlockId::new(1),
                    args: vec![v(4)],
                },
                &[],
            ),
        ];
        let mut exit = Block::new(trust_ir::BlockId::new(1)).with_param(v(15), Ty::I8);
        exit.body = vec![
            node(
                Inst::Assert {
                    cond: v(14),
                    kind: Default::default(),
                    site: None,
                },
                &[],
            ),
            node(
                Inst::Return {
                    values: vec![v(15)],
                },
                &[],
            ),
        ];
        module.functions.push(Function {
            id: FuncId::new(0),
            name: "shape".to_string(),
            ty: FuncTyId::new(0),
            entry: entry.id,
            blocks: vec![entry, exit],
            proofs: Vec::new(),
            calling_conv: trust_ir::CallingConv::default(),
            linkage: trust_ir::Linkage::default(),
            attrs: trust_ir::FuncAttrs::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
            body_gate: None,
            display_path: None,
            section: None,
            visibility: trust_ir::Visibility::default(),
            retained: false,
        });
        module
    }

    #[test]
    fn lowering_emits_only_wrapping_bit_vector_nodes() {
        let module = every_admitted_shape();
        let body = check_function(&module, &module.functions[0]).expect("admitted shape");
        let end = body.positions.values().copied().max().unwrap_or(0) + 1;
        for query in [
            site_query(&body, end, trust_ir::BlockId::new(1), 0, ValueId::new(14)),
            premise_query(&body, end, trust_ir::BlockId::new(1), 0),
        ] {
            for variable in &query.variables {
                assert!(matches!(
                    variable.ty,
                    TrustVcType::Bool | TrustVcType::Int { .. } | TrustVcType::Uint { .. }
                ));
            }
            assert!(!query.obligations.is_empty());
            for obligation in &query.obligations {
                for forbidden in [
                    "__",
                    "calc_",
                    "loop_",
                    "post_loop",
                    "_step_",
                    "requires",
                    "body_axiom",
                    "assertion_",
                    "assumption_",
                    "_dom",
                    "_unreachable",
                ] {
                    assert!(
                        !obligation.name().contains(forbidden),
                        "{} contains {forbidden}",
                        obligation.name()
                    );
                }
                assert_bv_only(obligation.expr());
            }
            let context = query.into_context();
            assert_eq!(context.overflow_behavior(), OverflowBehavior::Allow);
            assert_eq!(context.div0_behavior(), Div0Behavior::Allow);
        }
    }

    #[test]
    fn site_query_contains_only_the_strict_prefix() {
        let module = every_admitted_shape();
        let body = check_function(&module, &module.functions[0]).expect("admitted shape");
        // The Assert at bb0 index 10: the Assume at index 2 is a premise,
        // nothing from index 10 on is present, and the Br binding of %15 is
        // absent.
        let position = body.positions[&(trust_ir::BlockId::new(0), 10)];
        let query = site_query(
            &body,
            position,
            trust_ir::BlockId::new(0),
            10,
            ValueId::new(11),
        );
        let names = query
            .obligations
            .iter()
            .map(|obligation| obligation.name().to_string())
            .collect::<Vec<_>>();
        assert!(names.contains(&"tirb_asm_b0_i2".to_string()));
        assert!(names.contains(&"tirb_def_v11".to_string()));
        assert!(!names
            .iter()
            .any(|name| name == "tirb_def_v12" || name == "tirb_def_v15"));
        assert_eq!(names.last().map(String::as_str), Some("tirb_site_b0_i10"));
        assert!(!query.variables.iter().any(|v| v.name() == "tirb_v15"));
    }
}
