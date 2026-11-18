//! Native encoding of the separately admitted isolated BV language.
//!
//! No SMT text, ordinary mathematical query hypothesis, or surrounding solver
//! state enters this builder. Verdict acceptance stays in the shared query
//! envelope, including AY's strict model gate for counterexamples.

use std::collections::HashMap;

use ay_dpll::api::{Sort as AySort, Term as AyTerm};
use num_bigint::BigInt;
use trust_vc_bitvector::{Op, Query, Sort, Term};

use super::timeout::effective_conflict_budget;
use crate::counterexample_names::CounterexampleVarMeta;
use crate::encoder::AYEncoder;
use crate::ir::TrustVcType;
use crate::query::Limits;
use crate::solver_budget::ConflictBudget;
use crate::vc::VariableDecl;

fn native_sort(sort: Sort) -> AySort {
    match sort {
        Sort::Bool => AySort::Bool,
        Sort::Bits(width) => AySort::bitvec(width),
    }
}

struct Builder<'a> {
    encoder: &'a mut AYEncoder,
    variables: HashMap<String, AyTerm>,
}

impl Builder<'_> {
    fn term(&mut self, term: &Term) -> Result<AyTerm, String> {
        match term {
            Term::Shared(term) => self.term(term),
            Term::Euclidean(operation) => self.term(operation.expanded()),
            Term::Bool(value) => Ok(self.encoder.solver.bool_const(*value)),
            Term::Bits { value, width } => {
                let magnitude = BigInt::from(value.magnitude);
                let value = if value.negative {
                    -magnitude
                } else {
                    magnitude
                };
                self.encoder
                    .solver
                    .try_bv_const_bigint(&value, *width)
                    .map_err(|error| error.to_string())
            }
            Term::Var(name) => self
                .variables
                .get(name)
                .copied()
                .ok_or_else(|| format!("undeclared isolated BV variable '{name}'")),
            Term::If {
                condition,
                then_term,
                else_term,
            } => {
                let condition = self.term(condition)?;
                let then_term = self.term(then_term)?;
                let else_term = self.term(else_term)?;
                self.encoder
                    .solver
                    .try_ite(condition, then_term, else_term)
                    .map_err(|error| error.to_string())
            }
            Term::Let { name, value, body } => {
                let value = self.term(value)?;
                let old = self.variables.insert(name.clone(), value);
                let result = self.term(body);
                if let Some(old) = old {
                    self.variables.insert(name.clone(), old);
                } else {
                    self.variables.remove(name);
                }
                result
            }
            Term::Quant {
                forall,
                binders,
                body,
                triggers,
            } => {
                let mut saved = Vec::new();
                let mut native_binders = Vec::new();
                let result = (|| {
                    for (name, sort) in binders {
                        let value = self
                            .encoder
                            .solver
                            .try_fresh_var("bv_bound", native_sort(*sort))
                            .map_err(|error| error.to_string())?;
                        saved.push((name, self.variables.insert(name.clone(), value)));
                        native_binders.push(value);
                    }
                    let body = self.term(body)?;
                    let mut native_triggers = Vec::new();
                    for group in triggers {
                        let mut terms = Vec::new();
                        for pattern in group {
                            terms.push(self.term(pattern)?);
                        }
                        native_triggers.push(terms);
                    }
                    let borrowed: Vec<&[AyTerm]> =
                        native_triggers.iter().map(Vec::as_slice).collect();
                    let encoded = if *forall {
                        self.encoder.solver.try_forall_with_triggers(
                            &native_binders,
                            body,
                            &borrowed,
                        )
                    } else {
                        self.encoder.solver.try_exists_with_triggers(
                            &native_binders,
                            body,
                            &borrowed,
                        )
                    }
                    .map_err(|error| error.to_string())?;
                    // AY77 skips non-App roots (including a simplified variable,
                    // constant, Not or ITE). Never silently lose a source pattern.
                    // These fresh variables are not declared constants, so its
                    // native binder API preserves their exact term identities.
                    if self.encoder.solver.quantifier_triggers(encoded).as_ref()
                        != Some(&native_triggers)
                    {
                        return Err("native isolated BV encoding did not retain every exact trigger application".into());
                    }
                    Ok(encoded)
                })();
                for (name, old) in saved.into_iter().rev() {
                    if let Some(old) = old {
                        self.variables.insert(name.clone(), old);
                    } else {
                        self.variables.remove(name);
                    }
                }
                result
            }
            Term::App { op, args } => {
                // Admission has already checked every arity and sort. Keep
                // bounds checked here too so malformed callers fail closed.
                let left = self.term(args.first().ok_or("missing isolated BV operand")?)?;
                let right = if args.len() == 2 {
                    Some(self.term(&args[1])?)
                } else {
                    None
                };
                let solver = &mut self.encoder.solver;
                use Op::*;
                let encoded = match op {
                    Not => solver.try_not(left),
                    BitNot => solver.try_bvnot(left),
                    ZeroExtend(extra) => solver.try_bvzeroext(left, *extra),
                    SignExtend(extra) => solver.try_bvsignext(left, *extra),
                    Extract { high, low } => solver.try_bvextract(left, *high, *low),
                    _ => {
                        let right = right.ok_or("missing second isolated BV operand")?;
                        match op {
                            And => solver.try_and(left, right),
                            Or => solver.try_or(left, right),
                            Xor => solver.try_xor(left, right),
                            Implies => solver.try_implies(left, right),
                            BitAnd => solver.try_bvand(left, right),
                            BitOr => solver.try_bvor(left, right),
                            BitXor => solver.try_bvxor(left, right),
                            Add => solver.try_bvadd(left, right),
                            Sub => solver.try_bvsub(left, right),
                            Mul => solver.try_bvmul(left, right),
                            UDiv => solver.try_bvudiv(left, right),
                            URem => solver.try_bvurem(left, right),
                            SDiv => solver.try_bvsdiv(left, right),
                            SRem => solver.try_bvsrem(left, right),
                            Eq => solver.try_eq(left, right),
                            ULt => solver.try_bvult(left, right),
                            ULe => solver.try_bvule(left, right),
                            SLt => solver.try_bvslt(left, right),
                            SLe => solver.try_bvsle(left, right),
                            Shl => solver.try_bvshl(left, right),
                            LShr => solver.try_bvlshr(left, right),
                            AShr => solver.try_bvashr(left, right),
                            Not | BitNot | ZeroExtend(_) | SignExtend(_) | Extract { .. } => {
                                return Err("unexpected unary BV operator".into())
                            }
                        }
                    }
                };
                encoded.map_err(|error| error.to_string())
            }
        }
    }
}

pub(super) fn build(
    query: &Query,
    limits: &Limits,
    cores: bool,
) -> Result<(AYEncoder, HashMap<String, String>), String> {
    query.validate().map_err(str::to_owned)?;
    // A failed/unsupported bounded rewrite retains the original admitted
    // question. Native AY still establishes every resulting verdict.
    let rewritten = trust_vc_bitvector::congruence::simplify(query);
    let query = rewritten.as_ref().unwrap_or(query);
    let budget = effective_conflict_budget(limits.conflicts.map(ConflictBudget::Bounded));
    let mut encoder =
        AYEncoder::with_logic(ay_dpll::api::Logic::All).with_limits(limits.wall_ms, budget, 512);
    encoder.solver.set_produce_unsat_cores(cores);
    let mut variables = HashMap::new();
    for (name, sort) in &query.variables {
        let ty = match sort {
            Sort::Bool => TrustVcType::Bool,
            Sort::Bits(width) => TrustVcType::Uint { width: *width },
        };
        encoder
            .declare_variable(&VariableDecl::new(name.clone(), ty))
            .map_err(|error| error.to_string())?;
        variables.insert(
            name.clone(),
            *encoder
                .variables
                .get(name)
                .ok_or("missing declared BV variable")?,
        );
        encoder.counterexample_var_meta.insert(
            name.clone(),
            CounterexampleVarMeta {
                display_name: name.clone(),
                visible: true,
            },
        );
    }
    let mut labels = HashMap::new();
    {
        let mut builder = Builder {
            encoder: &mut encoder,
            variables,
        };
        for (index, requirement) in query.requires.iter().enumerate() {
            let term = builder.term(requirement)?;
            if cores {
                let name = format!("qh{index}");
                builder
                    .encoder
                    .solver
                    .try_assert_named(term, &name)
                    .map_err(|error| error.to_string())?;
                labels.insert(name, format!("requires[{index}]"));
            } else {
                builder
                    .encoder
                    .solver
                    .try_assert_term(term)
                    .map_err(|error| error.to_string())?;
            }
        }
        let goal = builder.term(&query.goal)?;
        let negated = builder
            .encoder
            .solver
            .try_not(goal)
            .map_err(|error| error.to_string())?;
        builder
            .encoder
            .solver
            .try_assert_term(negated)
            .map_err(|error| error.to_string())?;
    }
    Ok((encoder, labels))
}

#[cfg(test)]
mod trigger_tests {
    use super::*;

    fn app(op: Op, left: Term, right: Term) -> Term {
        Term::App {
            op,
            args: vec![left, right],
        }
    }

    #[test]
    fn native_multi_patterns_keep_actual_bound_handles_and_restore_the_outer_scope() {
        let x = Term::Var("x".into());
        let y = Term::Var("y".into());
        let term = Term::Quant {
            forall: true,
            binders: vec![("x".into(), Sort::Bits(8)), ("y".into(), Sort::Bits(8))],
            body: Box::new(app(Op::Eq, x.clone(), y.clone())),
            triggers: vec![
                vec![app(Op::BitAnd, x.clone(), y.clone())],
                vec![app(Op::BitOr, x.clone(), y.clone()), app(Op::BitXor, x, y)],
            ],
        };
        Query {
            variables: vec![("x".into(), Sort::Bool)],
            requires: vec![],
            goal: term.clone(),
            architecture: 64,
        }
        .validate()
        .unwrap();
        let mut encoder = AYEncoder::with_logic(ay_dpll::api::Logic::All);
        let outer = encoder.solver.try_fresh_var("outer", AySort::Bool).unwrap();
        let mut builder = Builder {
            encoder: &mut encoder,
            variables: HashMap::from([("x".into(), outer)]),
        };
        let encoded = builder.term(&term).unwrap();
        assert_eq!(builder.variables, HashMap::from([("x".into(), outer)]));
        let groups = builder.encoder.solver.quantifier_triggers(encoded).unwrap();
        assert_eq!(groups.iter().map(Vec::len).collect::<Vec<_>>(), [1, 2]);
        let arguments = [
            builder.encoder.solver.app_arg(groups[0][0], 0).unwrap(),
            builder.encoder.solver.app_arg(groups[0][0], 1).unwrap(),
        ];
        assert_ne!(arguments[0], arguments[1]);
        for group in groups {
            for pattern in group {
                assert_eq!(builder.encoder.solver.term_sort(pattern), AySort::bitvec(8));
                assert_eq!(builder.encoder.solver.app_num_args(pattern), 2);
                for index in 0..2 {
                    let argument = builder.encoder.solver.app_arg(pattern, index).unwrap();
                    assert!(arguments.contains(&argument));
                    assert_ne!(argument, outer);
                    assert_eq!(
                        builder.encoder.solver.term_sort(argument),
                        AySort::bitvec(8)
                    );
                }
            }
        }
    }

    #[test]
    fn a_pattern_normalized_to_a_constant_is_refused_instead_of_erased() {
        let zero = Term::Bits {
            value: trust_vc_bitvector::IntLit {
                negative: false,
                magnitude: 0,
            },
            width: 8,
        };
        let term = Term::Quant {
            forall: true,
            binders: vec![("x".into(), Sort::Bits(8))],
            body: Box::new(Term::Bool(false)),
            triggers: vec![vec![app(Op::BitAnd, Term::Var("x".into()), zero)]],
        };
        let question = Query {
            variables: vec![],
            requires: vec![],
            goal: term.clone(),
            architecture: 64,
        };
        question.validate().unwrap();
        let mut encoder = AYEncoder::with_logic(ay_dpll::api::Logic::All);
        let mut builder = Builder {
            encoder: &mut encoder,
            variables: HashMap::new(),
        };
        let error = builder.term(&term).unwrap_err();
        assert_eq!(
            error,
            "native isolated BV encoding did not retain every exact trigger application"
        );
        assert!(builder.variables.is_empty());
    }

    #[test]
    fn nested_native_binders_cannot_lend_their_sort_or_handle_to_outer_patterns() {
        let pattern = |width| {
            app(
                Op::BitAnd,
                Term::Var("x".into()),
                Term::Bits {
                    value: trust_vc_bitvector::IntLit {
                        negative: false,
                        magnitude: 1,
                    },
                    width,
                },
            )
        };
        let inner = Term::Quant {
            forall: false,
            binders: vec![("x".into(), Sort::Bits(8))],
            body: Box::new(app(
                Op::Eq,
                Term::Var("x".into()),
                Term::Bits {
                    value: trust_vc_bitvector::IntLit {
                        negative: false,
                        magnitude: 2,
                    },
                    width: 8,
                },
            )),
            triggers: vec![vec![pattern(8)]],
        };
        let term = Term::Quant {
            forall: true,
            binders: vec![("x".into(), Sort::Bits(32))],
            body: Box::new(inner),
            triggers: vec![vec![pattern(32)]],
        };
        Query {
            variables: vec![],
            requires: vec![],
            goal: term.clone(),
            architecture: 32,
        }
        .validate()
        .unwrap();
        let mut encoder = AYEncoder::with_logic(ay_dpll::api::Logic::All);
        let mut builder = Builder {
            encoder: &mut encoder,
            variables: HashMap::new(),
        };
        let encoded = builder.term(&term).unwrap();
        let groups = builder.encoder.solver.quantifier_triggers(encoded).unwrap();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].len(), 1);
        assert_eq!(
            builder.encoder.solver.term_sort(groups[0][0]),
            AySort::bitvec(32)
        );
        assert!(builder.variables.is_empty());
    }
}
