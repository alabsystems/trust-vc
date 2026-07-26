// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Expression, pattern, and place writers for cache canonical serialization.
//!
//! Split from `cache_canonical.rs` — Part of #2640.

use std::fmt::Write as FmtWrite;

use crate::ir::{MatchPattern, TrustVcExpr};
use crate::ir_expr::{IntConstKind, QuantifierKind, WrappingMode};
use crate::ir_place::TrustVcPlace;

pub(super) fn write_expr(out: &mut String, expr: &TrustVcExpr) {
    match expr {
        TrustVcExpr::UnitLit => {
            let _ = write!(out, "(UnitLit)");
        }
        TrustVcExpr::BoolLit(b) => {
            let _ = write!(out, "(BoolLit {b})");
        }
        TrustVcExpr::StringLit(value) => {
            let _ = write!(out, "(StringLit {:?})", value);
        }
        TrustVcExpr::IntLit { value, ty } => {
            let _ = write!(out, "(IntLit {value} {})", ty.to_type_string());
        }
        TrustVcExpr::Var { name, ty } => {
            let _ = write!(out, "(Var {name} {})", ty.to_type_string());
        }
        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => {
            let _ = write!(out, "(Arith {op} ");
            write_expr(out, left);
            let _ = write!(out, " ");
            write_expr(out, right);
            let _ = write!(out, " {})", ty.to_type_string());
        }
        TrustVcExpr::Neg(inner) => {
            let _ = write!(out, "(Neg ");
            write_expr(out, inner);
            let _ = write!(out, ")");
        }
        TrustVcExpr::Compare { op, left, right } => {
            let _ = write!(out, "(Compare {op} ");
            write_expr(out, left);
            let _ = write!(out, " ");
            write_expr(out, right);
            let _ = write!(out, ")");
        }
        TrustVcExpr::Logic { op, left, right } => {
            let _ = write!(out, "(Logic {op} ");
            write_expr(out, left);
            let _ = write!(out, " ");
            write_expr(out, right);
            let _ = write!(out, ")");
        }
        TrustVcExpr::Not(inner) => {
            let _ = write!(out, "(Not ");
            write_expr(out, inner);
            let _ = write!(out, ")");
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            let _ = write!(out, "(Implies ");
            write_expr(out, premise);
            let _ = write!(out, " ");
            write_expr(out, conclusion);
            let _ = write!(out, ")");
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => {
            let _ = write!(out, "(Ite ");
            write_expr(out, cond);
            let _ = write!(out, " ");
            write_expr(out, then_branch);
            let _ = write!(out, " ");
            write_expr(out, else_branch);
            let _ = write!(out, " {})", ty.to_type_string());
        }
        TrustVcExpr::Match {
            scrutinee,
            arms,
            ty,
        } => {
            let _ = write!(out, "(Match ");
            write_expr(out, scrutinee);
            let _ = write!(out, " {} {}", arms.len(), ty.to_type_string());
            for arm in arms {
                let _ = write!(out, " (arm ");
                write_pattern(out, &arm.pattern);
                let _ = write!(out, " ");
                write_expr(out, &arm.body);
                // The guard is part of the arm's semantics — serialize it so two
                // matches differing only in a guard do NOT collide on the VC-result
                // cache key (a collision would replay one's verdict for the other =
                // cache-poisoning false-verify).
                match &arm.guard {
                    Some(guard) => {
                        let _ = write!(out, " (guard ");
                        write_expr(out, guard);
                        let _ = write!(out, ")");
                    }
                    None => {
                        let _ = write!(out, " noguard");
                    }
                }
                let _ = write!(out, ")");
            }
            let _ = write!(out, ")");
        }
        TrustVcExpr::Let {
            name,
            ty,
            value,
            body,
        } => {
            let _ = write!(out, "(Let {name} {} ", ty.to_type_string());
            write_expr(out, value);
            let _ = write!(out, " ");
            write_expr(out, body);
            let _ = write!(out, ")");
        }
        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } => {
            let _ = write!(
                out,
                "(Cast {} {} ",
                from_ty.to_type_string(),
                to_ty.to_type_string()
            );
            write_expr(out, expr);
            let _ = write!(out, ")");
        }
        TrustVcExpr::CollectionOp {
            op,
            receiver,
            receiver_name,
            args,
            ty,
        } => {
            let _ = write!(out, "(CollOp {:?} ", op);
            write_expr(out, receiver);
            let _ = write!(out, " recv:{:?} args:{}", receiver_name, args.len());
            for arg in args {
                let _ = write!(out, " ");
                write_expr(out, arg);
            }
            let _ = write!(out, " {})", ty.to_type_string());
        }
        TrustVcExpr::Index {
            receiver,
            index,
            receiver_name,
            elem_ty,
        } => {
            let _ = write!(out, "(Index ");
            write_expr(out, receiver);
            let _ = write!(out, " ");
            write_expr(out, index);
            let _ = write!(
                out,
                " recv:{:?} {})",
                receiver_name,
                elem_ty.to_type_string()
            );
        }
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            triggers,
            trigger_inference_mode,
        } => {
            let kind_tag = match kind {
                QuantifierKind::Forall => "Forall",
                QuantifierKind::Exists => "Exists",
            };
            let _ = write!(out, "(Quant {kind_tag} [");
            for (i, (name, ty)) in bound_vars.iter().enumerate() {
                if i > 0 {
                    let _ = write!(out, ",");
                }
                let _ = write!(out, "{}:{}", name, ty.to_type_string());
            }
            let _ = write!(out, "] ");
            write_expr(out, body);
            match triggers {
                Some(groups) => {
                    let _ = write!(out, " triggers:{}", groups.len());
                    for group in groups {
                        let _ = write!(out, " [");
                        for (i, t) in group.iter().enumerate() {
                            if i > 0 {
                                let _ = write!(out, ",");
                            }
                            write_expr(out, t);
                        }
                        let _ = write!(out, "]");
                    }
                }
                None => {
                    let _ = write!(out, " triggers:none");
                }
            }
            let ti_tag = match trigger_inference_mode {
                Some(crate::trigger_inference::TriggerInferenceMode::Conservative) => {
                    "Conservative"
                }
                Some(crate::trigger_inference::TriggerInferenceMode::Aggressive) => "Aggressive",
                None => "none",
            };
            let _ = write!(out, " ti:{ti_tag})");
        }
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            let _ = write!(out, "(FnCall {name} {}", return_ty.to_type_string());
            for arg in args {
                let _ = write!(out, " ");
                write_expr(out, arg);
            }
            let _ = write!(out, ")");
        }
        TrustVcExpr::SpecClosure { params, body, ty } => {
            let _ = write!(out, "(SpecClosure [");
            for (i, (name, ty)) in params.iter().enumerate() {
                if i > 0 {
                    let _ = write!(out, ",");
                }
                let _ = write!(out, "{}:{}", name, ty.to_type_string());
            }
            let _ = write!(out, "] {} ", ty.to_type_string());
            write_expr(out, body);
            let _ = write!(out, ")");
        }
        TrustVcExpr::IntConst { ty, kind } => {
            let kind_tag = match kind {
                IntConstKind::Min => "Min",
                IntConstKind::Max => "Max",
            };
            let _ = write!(out, "(IntConst {} {kind_tag})", ty.to_type_string());
        }
        TrustVcExpr::SpecialArith {
            op,
            left,
            right,
            ty,
        } => {
            let _ = write!(out, "(SpecialArith {op} ");
            write_expr(out, left);
            let _ = write!(out, " ");
            write_expr(out, right);
            let _ = write!(out, " {})", ty.to_type_string());
        }
        TrustVcExpr::WrappingArith {
            mode,
            op,
            left,
            right,
            ty,
        } => {
            let mode_tag = match mode {
                WrappingMode::Wrapping => "Wrapping",
                WrappingMode::Checked => "Checked",
                WrappingMode::Saturating => "Saturating",
            };
            let _ = write!(out, "(WrappingArith {mode_tag} {op} ");
            write_expr(out, left);
            let _ = write!(out, " ");
            write_expr(out, right);
            let _ = write!(out, " {})", ty.to_type_string());
        }
        TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition,
            key,
            also_assert,
        } => {
            let _ = write!(out, "(Choose {var_name} {} {key} ", var_ty.to_type_string());
            write_expr(out, condition);
            if let Some(extra) = also_assert {
                let _ = write!(out, " also=");
                write_expr(out, extra);
            }
            let _ = write!(out, ")");
        }
        TrustVcExpr::ReadPlace { place, ty } => {
            let _ = write!(out, "(ReadPlace ");
            write_place(out, place);
            let _ = write!(out, " {})", ty.to_type_string());
        }
        TrustVcExpr::PlaceDisjoint { left, right } => {
            let _ = write!(out, "(PlaceDisjoint ");
            write_place(out, left);
            let _ = write!(out, " ");
            write_place(out, right);
            let _ = write!(out, ")");
        }
        TrustVcExpr::ProphecyNew { name, ty } => {
            let _ = write!(out, "(ProphecyNew {name} {})", ty.to_type_string());
        }
        TrustVcExpr::ProphecyResolve { name, value } => {
            let _ = write!(out, "(ProphecyResolve {name} ");
            write_expr(out, value);
            let _ = write!(out, ")");
        }
    }
}

fn write_pattern(out: &mut String, pattern: &MatchPattern) {
    match pattern {
        MatchPattern::Lit(expr) => {
            let _ = write!(out, "(PatLit ");
            write_expr(out, expr);
            let _ = write!(out, ")");
        }
        MatchPattern::Ident(name) => {
            let _ = write!(out, "(PatIdent {name})");
        }
        MatchPattern::Constructor {
            variant_name,
            bindings,
            has_rest,
        } => {
            let _ = write!(
                out,
                "(PatCtor {variant_name} [{}] rest:{has_rest})",
                bindings.join(",")
            );
        }
        MatchPattern::Struct {
            variant_name,
            fields,
            has_rest,
        } => {
            let _ = write!(out, "(PatStruct {variant_name} [");
            for (i, field) in fields.iter().enumerate() {
                if i > 0 {
                    let _ = write!(out, ",");
                }
                let _ = write!(out, "{}:{:?}", field.field_name, field.binding);
            }
            let _ = write!(out, "] rest:{has_rest})");
        }
        MatchPattern::Wildcard => {
            let _ = write!(out, "(PatWild)");
        }
        MatchPattern::Or(patterns) => {
            let _ = write!(out, "(PatOr");
            for p in patterns {
                let _ = write!(out, " ");
                write_pattern(out, p);
            }
            let _ = write!(out, ")");
        }
    }
}

fn write_place(out: &mut String, place: &TrustVcPlace) {
    let _ = write!(
        out,
        "(Place {} {} [",
        place.root_name,
        place.root_ty.to_type_string()
    );
    for (i, proj) in place.projections.iter().enumerate() {
        if i > 0 {
            let _ = write!(out, ",");
        }
        match proj {
            crate::ir_place::PlaceProjection::Field {
                field_name,
                field_ty,
            } => {
                let _ = write!(out, "Field({},{})", field_name, field_ty.to_type_string());
            }
            crate::ir_place::PlaceProjection::Index { index, elem_ty } => {
                let _ = write!(out, "Index(");
                write_expr(out, index);
                let _ = write!(out, ",{})", elem_ty.to_type_string());
            }
        }
    }
    let _ = write!(out, "] {})", place.place_ty.to_type_string());
}
