// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unwind conditions are pure entry-state contracts, not body expressions.
use super::*;
use crate::UnwindSpec;

enum Frame<'e> {
    Visit(&'e Expr),
    Bind(LocalId),
    Unbind(LocalId),
}

fn children<'e>(expression: &'e Expr, work: &mut Vec<Frame<'e>>) {
    let start = work.len();
    expression.for_each_child(&mut |child| work.push(Frame::Visit(child)));
    work[start..].reverse();
}

impl FnChecker<'_, '_> {
    pub(super) fn check_unwind(&mut self) {
        let decl = self.decl;
        let Some(unwind) = &decl.unwind else {
            return;
        };
        if decl.mode != Mode::Exec {
            self.report(
                WfClass::User,
                decl.span,
                "an 'unwind' specification can only be given on exec functions",
            );
        }
        if !matches!(decl.kind, FnKind::Function | FnKind::ConstFunction) {
            self.malformed(
                decl.span,
                "a non-function declaration carries an unwind contract",
            );
        }
        if let UnwindSpec::NoUnwindWhen(condition) = unwind {
            self.check_bool(condition, false);
            self.unwind_prestate(condition);
        }
    }

    fn unwind_prestate(&mut self, expression: &Expr) {
        // These are ordinary lookup structures, not admission or ownership tokens.
        let parameters: HashSet<LocalId> = self.decl.params.iter().copied().collect();
        let mut bound: HashMap<LocalId, usize> = HashMap::new();
        let mut work = vec![Frame::Visit(expression)];
        while let Some(frame) = work.pop() {
            let expression = match frame {
                Frame::Visit(expression) => expression,
                Frame::Bind(local) => {
                    *bound.entry(local).or_default() += 1;
                    continue;
                }
                Frame::Unbind(local) => {
                    if let Some(count) = bound.get_mut(&local) {
                        *count -= 1;
                        if *count == 0 {
                            bound.remove(&local);
                        }
                    }
                    continue;
                }
            };
            match &expression.kind {
                ExprKind::Read(place) | ExprKind::Old(place) => {
                    if !parameters.contains(&place.local) && !bound.contains_key(&place.local) {
                        self.malformed(
                            expression.span,
                            "an unwind condition reads a local outside its entry-state parameters and binders",
                        );
                    }
                    if matches!(&expression.kind, ExprKind::Read(_))
                        && self
                            .decl
                            .local(place.local)
                            .is_some_and(|local| matches!(local.ty, Ty::Ref { mutable: true, .. }))
                    {
                        self.malformed(
                            expression.span,
                            "an unwind condition reads a mutable-reference parameter without old",
                        );
                    }
                }
                ExprKind::Let { local, value, body } => {
                    // The initializer uses the outer scope, then the body sees
                    // this binding. Counts retain an outer binding of the same ID.
                    work.push(Frame::Unbind(*local));
                    work.push(Frame::Visit(body));
                    work.push(Frame::Bind(*local));
                    work.push(Frame::Visit(value));
                }
                ExprKind::Quant { vars, .. }
                | ExprKind::Choose { vars, .. }
                | ExprKind::UntriggeredQuant { vars, .. }
                | ExprKind::UntriggeredChoose { vars, .. } => {
                    for (local, _) in vars {
                        work.push(Frame::Unbind(*local));
                    }
                    children(expression, &mut work);
                    for (local, _) in vars.iter().rev() {
                        work.push(Frame::Bind(*local));
                    }
                }
                _ => children(expression, &mut work),
            }
        }
    }
}
