//! Completed ordinary-match observations from the current native body.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Debug)]
pub(crate) struct MatchUse<'tcx> {
    expression: &'tcx hir::Expr<'tcx>,
    scrutinee: &'tcx hir::Expr<'tcx>,
    arms: &'tcx [hir::Arm<'tcx>],
    native_match_owner: LocalDefId,
    native_match_body: &'tcx hir::Body<'tcx>,
    pub(crate) scrutinee_mode: Mode,
    /// The result of the completed ordinary arm-mode walk. A tracked input
    /// may produce a Spec observation, so the scrutinee mode cannot replace it.
    pub(crate) result_mode: Mode,
}

#[derive(Clone)]
pub(crate) struct MatchFacts<'tcx> {
    tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
    owner: LocalDefId,
    body: Option<&'tcx hir::Body<'tcx>>,
    entries: HashMap<HirId, MatchUse<'tcx>>,
}

impl std::fmt::Debug for MatchFacts<'_> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("MatchFacts")
            .field("definition", &self.definition)
            .field("owner", &self.owner)
            .field("entries", &self.entries.len())
            .finish_non_exhaustive()
    }
}

impl<'tcx> MatchFacts<'tcx> {
    pub(super) fn new(tcx: TyCtxt<'tcx>, definition: LocalDefId, owner: LocalDefId) -> Self {
        Self {
            tcx,
            definition,
            owner,
            body: tcx.hir_maybe_body_owned_by(owner),
            entries: HashMap::new(),
        }
    }

    fn current(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<(), String> {
        if !std::ptr::eq(*self.tcx, *tcx)
            || self.definition != definition
            || self.owner != owner
            || tcx.dcx().has_errors().is_some()
            || crate::reader::function_identity_observer::body_is_quarantined(tcx.sess, owner)
            || !self.body.is_some_and(|body| {
                tcx.hir_maybe_body_owned_by(owner)
                    .is_some_and(|actual| std::ptr::eq(body, actual))
            })
        {
            return Err("match facts belong to another native context or body".into());
        }
        Ok(())
    }

    pub(super) fn checked(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<(), String> {
        self.current(tcx, definition, owner)?;
        for item in self.entries.values() {
            self.for_match(
                tcx,
                definition,
                owner,
                tcx.typeck(owner),
                item.expression,
                item.scrutinee,
                item.arms,
            )?;
        }
        Ok(())
    }

    pub(crate) fn for_match(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        typeck: &'tcx TypeckResults<'tcx>,
        expression: &hir::Expr<'tcx>,
        scrutinee: &hir::Expr<'tcx>,
        arms: &[hir::Arm<'tcx>],
    ) -> Result<&MatchUse<'tcx>, String> {
        self.current(tcx, definition, owner)?;
        if expression.hir_id.owner.def_id != owner
            || !std::ptr::eq(typeck, tcx.typeck(owner))
            || !matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
        {
            return Err(
                "a match replaced its original native expression or type-check results".into(),
            );
        }
        let item = self
            .entries
            .get(&expression.hir_id)
            .ok_or("the original match has no completed mode observation")?;
        if !std::ptr::eq(item.expression, expression)
            || !std::ptr::eq(item.scrutinee, scrutinee)
            || item.arms.len() != arms.len()
            || item.arms.iter().zip(arms).any(|(a, b)| !std::ptr::eq(a, b))
            || tcx.hir_enclosing_body_owner(expression.hir_id) != item.native_match_owner
            || crate::reader::function_identity_observer::body_is_quarantined(
                tcx.sess,
                item.native_match_owner,
            )
            || !tcx
                .hir_maybe_body_owned_by(item.native_match_owner)
                .is_some_and(|body| std::ptr::eq(body, item.native_match_body))
            || tcx
                .ensure_result()
                .check_match(item.native_match_owner)
                .is_err()
        {
            return Err("a match changed its checked arms or native exhaustiveness result".into());
        }
        Ok(item)
    }
}

impl<'tcx> Checker<'_, 'tcx> {
    pub(super) fn ordinary_match(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        scrutinee: &'tcx hir::Expr<'tcx>,
        arms: &'tcx [hir::Arm<'tcx>],
        source: hir::MatchSource,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        if source != hir::MatchSource::Normal || arms.is_empty() || arms.len() > 1024 {
            return self.unknown("an empty, desugared or oversized match", expression.span);
        }
        if expression.hir_id.owner.def_id != self.body_owner
            || !matches!(self.tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
            || self
                .tcx
                .ensure_result()
                .check_match(self.tcx.hir_enclosing_body_owner(expression.hir_id))
                .is_err()
        {
            return self.unknown(
                "a match without its original native exhaustiveness check",
                expression.span,
            );
        }
        if arms.iter().any(|arm| arm.guard.is_some()) {
            return self.unknown(
                "a match guard is outside the current native slice",
                expression.span,
            );
        }
        // A match consumes a place once; unlike an operator its scrutinee is
        // not first coerced to the expected mode of the arm result.
        let scrutinee_mode = self.place_read(scrutinee, outer, Mode::Exec)?;
        if self.uses_ghost_blocks() && self.block == Ghostness::Exec && scrutinee_mode != Mode::Exec
        {
            return self.error(expression.span, "exec code cannot match on non-exec value");
        }
        let branch = if outer == Mode::Exec && scrutinee_mode != Mode::Exec {
            Mode::Proof
        } else {
            outer
        };
        let mut result = outer;
        for arm in arms {
            // HIR IDs are native owner-local identities. Retain mutations of
            // outer inferred bindings, but do not expose arm-local bindings
            // to later arms or the enclosing expression.
            let outer_ids: std::collections::HashSet<_> = self.vars.keys().copied().collect();
            let checked = (|| {
                self.match_pattern(arm.pat, scrutinee_mode, 0)?;
                self.expr(arm.body, branch, expect)
            })();
            self.vars.retain(|id, _| outer_ids.contains(id));
            result = join(result, checked?);
        }
        self.matches.entries.insert(
            expression.hir_id,
            MatchUse {
                expression,
                scrutinee,
                arms,
                scrutinee_mode,
                result_mode: result,
                native_match_owner: self.tcx.hir_enclosing_body_owner(expression.hir_id),
                native_match_body: self
                    .tcx
                    .hir_body_owned_by(self.tcx.hir_enclosing_body_owner(expression.hir_id)),
            },
        );
        Ok(result)
    }

    fn match_pattern(&mut self, pat: &'tcx hir::Pat<'tcx>, mode: Mode, depth: usize) -> M<()> {
        if depth > 64
            || !attrs::verus_attrs(self.tcx.hir_attrs(pat.hir_id)).is_empty()
            || pat.hir_id.owner.def_id != self.body_owner
            || !pat.default_binding_modes
            || !matches!(self.tcx.hir_node(pat.hir_id), hir::Node::Pat(actual) if std::ptr::eq(actual, pat))
            || self
                .typeck
                .pat_adjustments()
                .get(pat.hir_id)
                .is_some_and(|a| !a.is_empty())
        {
            return self.unknown(
                "a match pattern without its unadjusted native identity",
                pat.span,
            );
        }
        let mode = if self.in_pure { Mode::Spec } else { mode };
        match pat.kind {
            PatKind::Wild => Ok(()),
            PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) => {
                if !matches!(
                    self.typeck.pat_binding_modes().get(binding),
                    Some(BindingMode(ByRef::No, _))
                ) {
                    return self.unknown("a reference binding in a match", pat.span);
                }
                self.vars.insert(binding, VarMode::Mode(mode));
                self.bindings.record(pat, mode).map_err(|reason| {
                    Stop::Unknown(Refusal::new(TAG_MODES_UNKNOWN, reason, pat.span))
                })
            }
            PatKind::Tuple(parts, rest) => {
                let ty::Tuple(fields) = self.typeck.pat_ty(pat).kind() else {
                    return self.unknown("a tuple pattern with a different native type", pat.span);
                };
                if parts.len() > fields.len()
                    || (rest.as_opt_usize().is_none() && parts.len() != fields.len())
                {
                    return self.unknown("a tuple pattern with a different native arity", pat.span);
                }
                let gap = fields.len() - parts.len();
                for (position, part) in parts.iter().enumerate() {
                    let index = position
                        + if rest.as_opt_usize().is_some_and(|r| position >= r) {
                            gap
                        } else {
                            0
                        };
                    if self.typeck.pat_ty(part) != fields[index] {
                        return self
                            .unknown("a tuple pattern field has another native type", part.span);
                    }
                    self.match_pattern(part, mode, depth + 1)?;
                }
                Ok(())
            }
            PatKind::Expr(pat_expr) => match pat_expr.kind {
                hir::PatExprKind::Lit { lit, .. } => {
                    if !matches!(
                        (&lit.node, self.typeck.pat_ty(pat).kind()),
                        (rustc_ast::LitKind::Bool(_), ty::Bool)
                            | (rustc_ast::LitKind::Int(..), ty::Int(_) | ty::Uint(_))
                    ) {
                        return self.unknown("a non-scalar literal match pattern", pat.span);
                    }
                    Ok(())
                }
                hir::PatExprKind::Path(ref path) => {
                    self.match_variant(pat, path, pat_expr.hir_id, &[], depth, mode)
                }
                _ => self.unknown("an unsupported native pattern expression", pat.span),
            },
            PatKind::TupleStruct(ref path, parts, rest) => {
                let (_, variant, _) = self.match_variant_shape(pat, path, pat.hir_id)?;
                if parts.len() > variant.fields.len()
                    || (rest.as_opt_usize().is_none() && parts.len() != variant.fields.len())
                {
                    return self
                        .unknown("a variant pattern with a different native arity", pat.span);
                }
                let gap = variant.fields.len() - parts.len();
                let selected: Vec<_> = parts
                    .iter()
                    .enumerate()
                    .map(|(pos, p)| {
                        (
                            pos + if rest.as_opt_usize().is_some_and(|r| pos >= r) {
                                gap
                            } else {
                                0
                            },
                            p,
                        )
                    })
                    .collect();
                self.match_variant(pat, path, pat.hir_id, &selected, depth, mode)
            }
            PatKind::Struct(ref path, fields, _) => {
                let mut selected = Vec::new();
                for field in fields {
                    let Some(index) = self.typeck.opt_field_index(field.hir_id) else {
                        return self
                            .unknown("a match field without a native field index", field.span);
                    };
                    selected.push((index.as_usize(), field.pat));
                }
                self.match_variant(pat, path, pat.hir_id, &selected, depth, mode)
            }
            _ => self.unknown(
                "a reference, alternative, range or binding-subpattern match",
                pat.span,
            ),
        }
    }

    fn match_variant_shape(
        &self,
        pat: &hir::Pat<'tcx>,
        path: &hir::QPath<'tcx>,
        resolution: HirId,
    ) -> M<(
        ty::AdtDef<'tcx>,
        &'tcx ty::VariantDef,
        ty::GenericArgs<'tcx>,
    )> {
        let ty::Adt(adt, arguments) = self.typeck.pat_ty(pat).kind() else {
            return self.unknown("a variant pattern without its native ADT", pat.span);
        };
        if !adt.is_enum() || !adt.did().is_local() || !self.cx.permits_variant_fields(adt.did()) {
            return self.unknown(
                "a match datatype outside its current local representation scope",
                pat.span,
            );
        }
        self.datatype_mode(*adt, pat.span)?;
        let Some((_, variant)) = super::super::datatypes::constructor_variant(
            *adt,
            self.typeck.qpath_res(path, resolution),
        ) else {
            return self.unknown(
                "a match constructor outside its actual native datatype",
                pat.span,
            );
        };
        Ok((*adt, variant, *arguments))
    }

    fn match_variant(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        path: &hir::QPath<'tcx>,
        resolution: HirId,
        selected: &[(usize, &'tcx hir::Pat<'tcx>)],
        depth: usize,
        mode: Mode,
    ) -> M<()> {
        let (_, variant, arguments) = self.match_variant_shape(pat, path, resolution)?;
        let mut seen = std::collections::HashSet::new();
        for (index, child) in selected {
            let Some(field) = variant.fields.iter().nth(*index) else {
                return self.unknown("a match field outside its native variant", child.span);
            };
            let environment = ty::TypingEnv::post_analysis(self.tcx, self.body_owner);
            let field_type = self
                .tcx
                .try_normalize_erasing_regions(environment, field.ty(self.tcx, arguments));
            let pattern_type = self.tcx.try_normalize_erasing_regions(
                environment,
                ty::Unnormalized::new(self.typeck.pat_ty(child)),
            );
            let (Ok(field_type), Ok(pattern_type)) = (field_type, pattern_type) else {
                return self.unknown(
                    "a native match field type cannot be normalized in its body",
                    child.span,
                );
            };
            if !seen.insert(*index) || pattern_type != field_type {
                return self.unknown(
                    "a duplicate or differently typed native match field",
                    child.span,
                );
            }
            let field_mode = self.constructor_field_mode(field, child.span)?;
            if self.uses_ghost_blocks()
                && self.block == Ghostness::Exec
                && field_mode != Mode::Exec
                && !matches!(
                    child.kind,
                    PatKind::Wild | PatKind::Binding(BindingMode(ByRef::No, _), _, _, None)
                )
            {
                return self.unknown("an exec match testing a ghost field", child.span);
            }
            self.match_pattern(child, join(mode, field_mode), depth + 1)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    extern crate rustc_driver;

    use super::*;
    use crate::reader::declaration_modes::DeclarationModes;
    use rustc_driver::{Callbacks, Compilation};
    use rustc_interface::interface::Compiler;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT: AtomicU64 = AtomicU64::new(0);

    struct Inspect(bool);
    impl Callbacks for Inspect {
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            assert!(tcx.dcx().has_errors().is_none());
            // This declaration-only component context supplies no body or
            // ownership authority. Even otherwise-refused tracked bodies
            // must retain their real completed expression-mode observation.
            let context = DeclarationModes::new(tcx);
            for (name, scrutinee_mode, result_mode) in [
                ("ExecResult", Mode::Exec, Mode::Exec),
                ("ProofResult", Mode::Proof, Mode::Proof),
                ("ProofToSpecResult", Mode::Proof, Mode::Spec),
                ("ExecToSpecResult", Mode::Exec, Mode::Spec),
                ("SpecResult", Mode::Spec, Mode::Spec),
            ] {
                let definition = tcx
                    .hir_crate_items(())
                    .owners()
                    .map(|owner| owner.def_id)
                    .find(|owner| {
                        tcx.opt_item_name(owner.to_def_id())
                            .is_some_and(|actual| actual.as_str() == name)
                    })
                    .unwrap();
                let facts = match context.check(definition) {
                    ModeCheck::Clean(facts) => facts,
                    other => panic!("{name} must complete its real mode walk: {other:?}"),
                };
                let mut expression = tcx.hir_body_owned_by(definition).value;
                loop {
                    match expression.kind {
                        hir::ExprKind::Block(block, None) if block.stmts.is_empty() => {
                            expression = block.expr.unwrap();
                        }
                        hir::ExprKind::DropTemps(inner) => expression = inner,
                        _ => break,
                    }
                }
                let hir::ExprKind::Match(scrutinee, arms, hir::MatchSource::Normal) =
                    expression.kind
                else {
                    panic!("{name} must retain its actual native match");
                };
                let observed = facts
                    .matches
                    .for_match(
                        tcx,
                        definition,
                        definition,
                        tcx.typeck(definition),
                        expression,
                        scrutinee,
                        arms,
                    )
                    .unwrap();
                assert_eq!(observed.scrutinee_mode, scrutinee_mode, "{name}");
                assert_eq!(observed.result_mode, result_mode, "{name}");
            }
            assert!(tcx.dcx().has_errors().is_none());
            self.0 = true;
            Compilation::Stop
        }
    }

    #[test]
    fn native_completed_match_result_modes_are_not_scrutinee_modes() {
        let directory = std::env::temp_dir().join(format!(
            "trust-vc-native-match-result-modes-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&directory).unwrap();
        let source = directory.join("test.rs");
        std::fs::write(
            &source,
            r#"#![feature(register_tool, stmt_expr_attributes)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, non_snake_case)]
#[verus::internal(verus_macro)]
fn ExecResult(b: bool) -> u8 { match b { true => 1, false => 2 } }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
#[verus::internal(returns(proof))]
fn ProofResult<T>(#[verus::internal(proof)] b: bool, #[verus::internal(proof)] value: T) -> T {
    match b { true => value, false => value }
}
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn ProofToSpecResult(#[verus::internal(proof)] b: bool, value: bool) -> bool {
    match b { true => value, false => value }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn SpecUnit() -> () { () }
#[verus::internal(verus_macro)]
fn ExecToSpecResult(b: bool) {
    #[verifier::proof_block] { match b { true => SpecUnit(), false => SpecUnit() } }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn SpecResult(b: bool, value: bool) -> bool { match b { true => value, false => value } }
"#,
        )
        .unwrap();
        let argv = vec![
            "native-match-result-mode-control".to_string(),
            "-Ztrust-verify=off".to_string(),
            "--sysroot".to_string(),
            env!("VC_SHIM_COMPILER_SYSROOT").to_string(),
            "--crate-type=lib".to_string(),
            "--crate-name=native_match_result_modes".to_string(),
            "--edition=2021".to_string(),
            "--emit=metadata".to_string(),
            "--out-dir".to_string(),
            directory.to_str().unwrap().to_string(),
            source.to_str().unwrap().to_string(),
        ];
        let mut inspect = Inspect(false);
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&argv, &mut inspect))
            .expect("the genuine native source must reach analysis without diagnostics");
        assert!(inspect.0);
        std::fs::remove_dir_all(directory).unwrap();
    }
}
