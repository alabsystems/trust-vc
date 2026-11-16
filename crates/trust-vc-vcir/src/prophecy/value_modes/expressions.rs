use super::*;

impl Walk<'_> {
    pub(super) fn expression(&mut self, expr: &Expr, state: &mut Vec<Origin>) -> Option<Class> {
        let mode = match &expr.kind {
            ExprKind::Lit(Lit::Unit) => Some(Class::NonSpec),
            ExprKind::Read(place) => self.read(state, place),
            ExprKind::Old(_) => Some(Class::Spec),
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                self.expression(cond, state);
                let mut yes = state.clone();
                let mut no = state.clone();
                let a = self.expression(then_expr, &mut yes);
                let b = self.expression(else_expr, &mut no);
                for ((slot, a), b) in state.iter_mut().zip(yes).zip(no) {
                    *slot = merge(a, b);
                }
                // Upstream If joins ARM modes only. A prophetic condition
                // changes prophecy, not this returned read mode.
                a.zip(b).map(|(a, b)| join(a, b))
            }
            ExprKind::Let { local, value, body } => {
                self.expression(value, state);
                let saved = state.get(local.index()).copied();
                if let Some(slot) = state.get_mut(local.index()) {
                    *slot = Origin::Invalid;
                }
                let mode = self.expression(body, state);
                if let (Some(slot), Some(saved)) = (state.get_mut(local.index()), saved) {
                    *slot = saved;
                }
                mode
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => {
                for arg in args {
                    self.expression(arg, state);
                }
                self.fns
                    .get(callee)
                    .filter(|callee| callee.mode == Mode::Spec)
                    .and_then(|callee| instantiated_return_mode(callee, type_args, &expr.ty))
                    .map(Class::from)
            }
            ExprKind::ProofInSpec(block) => {
                self.scoped(block, state);
                Some(Class::NonSpec)
            }
            ExprKind::ProofInSpecTail { block, tail } => {
                let saved = self.statements(block, state);
                let mode = self.expression(tail, state);
                for (local, origin) in saved.into_iter().rev() {
                    state[local] = origin;
                }
                mode
            }
            ExprKind::Field { base, .. } | ExprKind::TupleField { base, .. } => {
                self.expression(base, state);
                if self.known_projection_input(base, state) {
                    Some(Class::Spec)
                } else {
                    None
                }
            }
            ExprKind::MutRefCurrent(reference) | ExprKind::MutRefFuture(reference) => {
                self.expression(reference, state);
                Some(Class::Spec)
            }
            ExprKind::Choose { .. } => {
                expr.for_each_child(&mut |child| {
                    self.expression(child, state);
                });
                Some(Class::Spec)
            }
            _ => {
                expr.for_each_child(&mut |child| {
                    self.expression(child, state);
                });
                None
            }
        };
        if expr.ty == Ty::Unit {
            mode
        } else {
            None
        }
    }
}
