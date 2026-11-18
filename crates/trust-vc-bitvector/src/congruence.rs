//! Bounded scoped congruence for exact isolated BV arithmetic.
//!
//! Only this isolated query's positive dominating equations are used. Width,
//! extension and overflow semantics remain explicit; unsupported shapes fall
//! back to the unchanged native AY query.
use super::{integer::Euclidean, IntLit, Op, Query, Sort, Term, DEPTH, MAX_WIDTH, WORK};
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

#[derive(Clone, PartialEq, Eq, Hash)]
enum Kind {
    Bool(bool),
    Bits(IntLit, u32),
    Var(String),
    App(Op, Vec<usize>),
    Euclidean(usize),
}
#[derive(Clone, PartialEq, Eq, Hash)]
struct Node {
    sort: Sort,
    kind: Kind,
}
struct Engine<'a> {
    work: &'a mut usize,
    variables: HashMap<String, Sort>,
    nodes: Vec<Node>,
    ids: HashMap<Node, usize>,
    widths: Vec<u32>,
    divisions: Vec<Division>,
}

#[derive(Clone, Copy)]
struct Operand {
    node: usize,
    width: u32,
    signed: bool,
}

struct Division {
    operation: Arc<Euclidean>,
    operands: [Operand; 2],
}

#[derive(Clone, Default)]
struct Facts {
    equalities: Vec<(usize, usize)>,
    nonzero: Vec<usize>,
}

impl Facts {
    fn size(&self) -> Option<usize> {
        self.equalities
            .len()
            .checked_mul(2)?
            .checked_add(self.nonzero.len())
    }
}
impl Engine<'_> {
    fn pay(&mut self, amount: usize) -> Option<()> {
        let next = self.work.checked_sub(amount);
        *self.work = next.unwrap_or(0);
        next.map(|_| ())
    }
    fn intern(&mut self, node: Node) -> Option<usize> {
        let payload = match &node.kind {
            Kind::Var(name) => name.len(),
            Kind::App(_, args) => args.len(),
            Kind::Bits(_, width) => (*width as usize).div_ceil(64),
            Kind::Bool(_) | Kind::Euclidean(_) => 1,
        };
        self.pay(payload.checked_mul(2)?.checked_add(2)?)?;
        if let Some(id) = self.ids.get(&node) {
            return Some(*id);
        }
        let id = self.nodes.len();
        self.nodes.push(node.clone());
        self.ids.insert(node, id);
        Some(id)
    }
    fn app_sort(&mut self, op: Op, args: &[usize]) -> Option<Sort> {
        self.pay(args.len().checked_add(1)?)?;
        let unary = matches!(
            op,
            Op::Not | Op::BitNot | Op::ZeroExtend(_) | Op::SignExtend(_) | Op::Extract { .. }
        );
        if args.len() != if unary { 1 } else { 2 } {
            return None;
        }
        let a = self.nodes.get(args[0])?.sort;
        if unary {
            return match (op, a) {
                (Op::Not, Sort::Bool) => Some(Sort::Bool),
                (Op::BitNot, Sort::Bits(_)) => Some(a),
                (Op::ZeroExtend(extra) | Op::SignExtend(extra), Sort::Bits(w)) => {
                    let w = w.checked_add(extra)?;
                    (w <= MAX_WIDTH).then_some(Sort::Bits(w))
                }
                (Op::Extract { high, low }, Sort::Bits(w)) if low <= high && high < w => {
                    Some(Sort::Bits(high - low + 1))
                }
                _ => None,
            };
        }
        if self.nodes.get(args[1])?.sort != a {
            return None;
        }
        match (op, a) {
            (Op::Eq, _) => Some(Sort::Bool),
            (Op::And | Op::Or | Op::Xor | Op::Implies, Sort::Bool) => Some(Sort::Bool),
            (Op::ULt | Op::ULe | Op::SLt | Op::SLe, Sort::Bits(_)) => Some(Sort::Bool),
            (
                Op::BitAnd
                | Op::BitOr
                | Op::BitXor
                | Op::Add
                | Op::Sub
                | Op::Mul
                | Op::Shl
                | Op::LShr
                | Op::AShr,
                Sort::Bits(_),
            ) => Some(a),
            // Raw division nodes do not carry mathematical result semantics
            // or a Verus zero arm. Only Integer::euclidean supplies those.
            _ => None,
        }
    }
    fn extension(&self, id: usize) -> Option<(usize, bool)> {
        match &self.nodes.get(id)?.kind {
            Kind::App(Op::ZeroExtend(extra), args) if *extra > 0 && args.len() == 1 => {
                Some((args[0], false))
            }
            Kind::App(Op::SignExtend(extra), args) if *extra > 0 && args.len() == 1 => {
                Some((args[0], true))
            }
            _ => None,
        }
    }
    fn extend(&mut self, id: usize, width: u32, signed: bool) -> Option<usize> {
        self.pay((width as usize).div_ceil(64).checked_add(1)?)?;
        let Sort::Bits(old) = self.nodes.get(id)?.sort else {
            return None;
        };
        let extra = width.checked_sub(old)?;
        if extra == 0 {
            return Some(id);
        }
        self.app(
            if signed {
                Op::SignExtend(extra)
            } else {
                Op::ZeroExtend(extra)
            },
            vec![id],
        )
    }
    fn app(&mut self, op: Op, args: Vec<usize>) -> Option<usize> {
        let sort = self.app_sort(op, &args)?;
        if let Op::ZeroExtend(extra) | Op::SignExtend(extra) = op {
            let inner = args[0];
            if extra == 0 {
                return Some(inner);
            }
            if self.literal_zero(inner) {
                let Sort::Bits(width) = sort else {
                    return None;
                };
                return self.intern(Node {
                    sort,
                    kind: Kind::Bits(
                        IntLit {
                            negative: false,
                            magnitude: 0,
                        },
                        width,
                    ),
                });
            }
            let outer_signed = matches!(op, Op::SignExtend(_));
            self.pay(3)?;
            if let Some((base, inner_signed)) = self.extension(inner) {
                // sext(zext(x)) collapses only because the inner extension
                // added a real zero sign bit. zext(sext(x)) stays intact.
                if outer_signed || !inner_signed {
                    let Sort::Bits(width) = sort else {
                        return None;
                    };
                    return self.extend(base, width, outer_signed && inner_signed);
                }
            }
            if let Kind::App(Op::Mul, factors) = &self.nodes[inner].kind {
                if factors.len() != 2 {
                    return None;
                }
                let factors = [factors[0], factors[1]];
                self.pay(4)?;
                if let (Some((a, signed_a)), Some((b, signed_b))) =
                    (self.extension(factors[0]), self.extension(factors[1]))
                {
                    let (Sort::Bits(p), Sort::Bits(q), Sort::Bits(w), Sort::Bits(width)) = (
                        self.nodes[a].sort,
                        self.nodes[b].sort,
                        self.nodes[inner].sort,
                        sort,
                    ) else {
                        return None;
                    };
                    let full = p.checked_add(q)?;
                    // A p-bit by q-bit product is exact in p+q bits, signed
                    // iff either factor is signed. Viewing two unsigned
                    // factors as signed needs one MORE original bit.
                    let exact = full <= w
                        && if outer_signed {
                            signed_a || signed_b || full < w
                        } else {
                            !signed_a && !signed_b
                        };
                    if exact {
                        let a = self.extend(a, width, signed_a)?;
                        let b = self.extend(b, width, signed_b)?;
                        return self.app(Op::Mul, vec![a, b]);
                    }
                }
            }
        }
        self.intern(Node {
            sort,
            kind: Kind::App(op, args),
        })
    }
    fn term(&mut self, term: &Term, depth: usize) -> Option<usize> {
        self.pay(1)?;
        if depth > DEPTH {
            return None;
        }
        match term {
            Term::Shared(inner) => self.term(inner, depth + 1),
            Term::Euclidean(operation) => {
                let [(numerator, nw, ns), (denominator, dw, ds)] = operation.operands();
                let operands = [
                    Operand {
                        node: self.term(numerator, depth + 1)?,
                        width: nw,
                        signed: ns,
                    },
                    Operand {
                        node: self.term(denominator, depth + 1)?,
                        width: dw,
                        signed: ds,
                    },
                ];
                if operands
                    .iter()
                    .any(|operand| self.nodes[operand.node].sort != Sort::Bits(operand.width))
                {
                    return None;
                }
                let index = self.divisions.len();
                self.pay(5)?;
                self.divisions.push(Division {
                    operation: operation.clone(),
                    operands,
                });
                self.intern(Node {
                    sort: Sort::Bits(operation.result().0),
                    kind: Kind::Euclidean(index),
                })
            }
            Term::Bool(value) => self.intern(Node {
                sort: Sort::Bool,
                kind: Kind::Bool(*value),
            }),
            Term::Bits { value, width } => self.intern(Node {
                sort: Sort::Bits(*width),
                kind: Kind::Bits(*value, *width),
            }),
            Term::Var(name) => {
                let sort = *self.variables.get(name)?;
                self.pay(name.len().checked_add(1)?)?;
                self.intern(Node {
                    sort,
                    kind: Kind::Var(name.clone()),
                })
            }
            Term::App { op, args } => {
                self.pay(args.len().checked_add(1)?)?;
                let mut children = Vec::with_capacity(args.len());
                for arg in args {
                    children.push(self.term(arg, depth + 1)?);
                }
                self.app(*op, children)
            }
            Term::If { .. } | Term::Let { .. } | Term::Quant { .. } => None,
        }
    }
    fn literal_zero(&self, id: usize) -> bool {
        matches!(&self.nodes[id].kind, Kind::Bits(value, _) if value.magnitude == 0)
    }

    fn positive(&mut self, id: usize, facts: &mut Facts, depth: usize) -> Option<()> {
        self.pay(3)?;
        if depth > DEPTH {
            return None;
        }
        match &self.nodes[id].kind {
            Kind::App(Op::And, args) => {
                let (a, b) = (args[0], args[1]);
                self.positive(a, facts, depth + 1)?;
                self.positive(b, facts, depth + 1)?;
            }
            Kind::App(Op::Eq, args) => {
                let pair = (args[0], args[1]);
                self.pay(2)?;
                facts.equalities.push(pair);
            }
            Kind::App(Op::Not, args) => {
                if let Kind::App(Op::Eq, operands) = &self.nodes[args[0]].kind {
                    let (a, b) = (operands[0], operands[1]);
                    if self.literal_zero(a) {
                        facts.nonzero.push(b);
                    } else if self.literal_zero(b) {
                        facts.nonzero.push(a);
                    }
                }
            }
            _ => {}
        }
        Some(())
    }
    fn goal_widths(&mut self, id: usize, found: &mut BTreeSet<u32>, depth: usize) -> Option<()> {
        self.pay(2)?;
        if depth > DEPTH {
            return None;
        }
        if matches!(self.nodes[id].kind, Kind::Euclidean(_)) {
            let Sort::Bits(width) = self.nodes[id].sort else {
                return None;
            };
            found.insert(width);
            return Some(());
        }
        let Kind::App(op, args) = &self.nodes[id].kind else {
            return Some(());
        };
        let (op, sort) = (*op, self.nodes[id].sort);
        self.pay(args.len().checked_add(1)?)?;
        let args = match &self.nodes[id].kind {
            Kind::App(_, args) => args.clone(),
            _ => return None,
        };
        if op == Op::Mul {
            let Sort::Bits(width) = sort else {
                return None;
            };
            found.insert(width);
        }
        for arg in args {
            self.goal_widths(arg, found, depth + 1)?;
        }
        Some(())
    }
    fn classes(&mut self, facts: &[(usize, usize)], extra_widths: &[u32]) -> Option<Classes> {
        self.pay(
            facts
                .len()
                .checked_mul(2)?
                .checked_add(self.widths.len())?
                .checked_add(extra_widths.len())?,
        )?;
        let mut pairs = facts.to_vec();
        let mut widths = self.widths.clone();
        widths.extend(extra_widths);
        widths.sort_unstable();
        widths.dedup();
        for &(left, right) in facts {
            self.pay(2)?;
            let Sort::Bits(width) = self.nodes[left].sort else {
                continue;
            };
            for &target in &widths {
                self.pay(1)?;
                if target <= width {
                    continue;
                }
                // Equality is preserved by applying the SAME extension to
                // both sides. Use only widths required by a goal comparison.
                for signed in [false, true] {
                    let left = self.extend(left, target, signed)?;
                    let right = self.extend(right, target, signed)?;
                    self.pay(2)?;
                    pairs.push((left, right));
                }
            }
        }
        self.pay(self.nodes.len().checked_add(1)?)?;
        let mut classes = Classes {
            parents: (0..self.nodes.len()).collect(),
        };
        for (left, right) in pairs {
            classes.union(left, right, self.work)?;
        }
        loop {
            let mut changed = false;
            let mut applications = HashMap::new();
            for id in 0..self.nodes.len() {
                self.pay(2)?;
                if let Kind::App(op, args) = &self.nodes[id].kind {
                    let (op, sort) = (*op, self.nodes[id].sort);
                    self.pay(args.len().checked_mul(2)?.checked_add(1)?)?;
                    let args = match &self.nodes[id].kind {
                        Kind::App(_, args) => args,
                        _ => return None,
                    };
                    let mut children = Vec::with_capacity(args.len());
                    for &arg in args {
                        children.push(classes.find(arg, self.work)?);
                    }
                    let key = (sort, op, children);
                    if let Some(prior) = applications.insert(key, id) {
                        changed |= classes.union(prior, id, self.work)?;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        Some(classes)
    }

    fn euclidean_result(&self, id: usize) -> Option<usize> {
        let (term, extension) = match self.extension(id) {
            Some((term, signed)) => (term, Some(signed)),
            None => (id, None),
        };
        let Kind::Euclidean(index) = self.nodes[term].kind else {
            return None;
        };
        let exact_sign = self.divisions[index].operation.result().1;
        if extension.is_some_and(|signed| signed != exact_sign) {
            return None;
        }
        Some(index)
    }

    fn align_operands(&mut self, a: Operand, b: Operand) -> Option<(usize, usize, u32)> {
        let width = a
            .width
            .checked_add(u32::from(!a.signed && b.signed))?
            .max(b.width.checked_add(u32::from(a.signed && !b.signed))?);
        Some((
            self.extend(a.node, width, a.signed)?,
            self.extend(b.node, width, b.signed)?,
            width,
        ))
    }

    fn euclidean_equivalent(&mut self, a: usize, b: usize, facts: &Facts) -> Option<bool> {
        let (Some(a), Some(b)) = (self.euclidean_result(a), self.euclidean_result(b)) else {
            return Some(false);
        };
        if facts.nonzero.is_empty()
            || self.divisions[a].operation.is_remainder()
                != self.divisions[b].operation.is_remainder()
        {
            return Some(false);
        }
        let [left_numerator, left_denominator] = self.divisions[a].operands;
        let [right_numerator, right_denominator] = self.divisions[b].operands;
        let (ln, rn, nw) = self.align_operands(left_numerator, right_numerator)?;
        let (ld, rd, dw) = self.align_operands(left_denominator, right_denominator)?;
        // Either exact extension of a witnessed nonzero bit pattern stays
        // nonzero. Use only witnesses that can be compared losslessly here.
        self.pay(facts.nonzero.len().checked_mul(2)?)?;
        let mut nonzero = Vec::new();
        for &known in &facts.nonzero {
            let Sort::Bits(width) = self.nodes[known].sort else {
                continue;
            };
            if width > dw {
                continue;
            }
            nonzero.push(self.extend(known, dw, false)?);
            if width < dw {
                nonzero.push(self.extend(known, dw, true)?);
            }
        }
        let mut classes = self.classes(&facts.equalities, &[nw, dw])?;
        if !classes.same(ln, rn, self.work)? || !classes.same(ld, rd, self.work)? {
            return Some(false);
        }
        for known in nonzero {
            if classes.same(ld, known, self.work)? {
                return Some(true);
            }
        }
        Some(false)
    }
    fn boolean(&mut self, id: usize, facts: &Facts, depth: usize) -> Option<usize> {
        self.pay(2)?;
        if depth > DEPTH {
            return None;
        }
        let Kind::App(op, args) = &self.nodes[id].kind else {
            return Some(id);
        };
        let op = *op;
        self.pay(args.len().checked_add(1)?)?;
        let args = match &self.nodes[id].kind {
            Kind::App(_, args) => args.clone(),
            _ => return None,
        };
        if op == Op::Eq {
            let (a, b) = (args[0], args[1]);
            if self.euclidean_equivalent(a, b, facts)?
                || self
                    .classes(&facts.equalities, &[])?
                    .same(a, b, self.work)?
            {
                return self.intern(Node {
                    sort: Sort::Bool,
                    kind: Kind::Bool(true),
                });
            }
            return Some(id);
        }
        if !matches!(op, Op::And | Op::Or | Op::Xor | Op::Implies | Op::Not) {
            return Some(id);
        }
        let left = self.boolean(args[0], facts, depth + 1)?;
        if op == Op::Not {
            return self.app(op, vec![left]);
        }
        let right = if matches!(op, Op::And | Op::Implies) {
            self.pay(facts.size()?.checked_add(1)?)?;
            let mut scoped = facts.clone();
            self.positive(args[0], &mut scoped, depth + 1)?;
            self.boolean(args[1], &scoped, depth + 1)?
        } else {
            // A disjunction or XOR grants no facts to the other branch.
            self.boolean(args[1], facts, depth + 1)?
        };
        self.app(op, vec![left, right])
    }
    fn emit(&mut self, id: usize, memo: &mut [Option<Arc<Term>>], depth: usize) -> Option<Term> {
        self.pay(1)?;
        if depth > DEPTH {
            return None;
        }
        if let Some(term) = &memo[id] {
            return Some(Term::Shared(term.clone()));
        }
        let cost = match &self.nodes[id].kind {
            Kind::Var(name) => name.len(),
            Kind::App(_, args) => args.len(),
            _ => 1,
        };
        self.pay(cost.checked_mul(2)?.checked_add(1)?)?;
        let node = self.nodes[id].clone();
        let term = match node.kind {
            Kind::Bool(value) => Term::Bool(value),
            Kind::Bits(value, width) => Term::Bits { value, width },
            Kind::Var(name) => Term::Var(name),
            Kind::Euclidean(index) => Term::Euclidean(self.divisions[index].operation.clone()),
            Kind::App(op, args) => {
                let mut children = Vec::with_capacity(args.len());
                for arg in args {
                    children.push(self.emit(arg, memo, depth + 1)?);
                }
                Term::App { op, args: children }
            }
        };
        let term = Arc::new(term);
        memo[id] = Some(term.clone());
        Some(Term::Shared(term))
    }
}

struct Classes {
    parents: Vec<usize>,
}
impl Classes {
    fn find(&mut self, mut id: usize, work: &mut usize) -> Option<usize> {
        loop {
            let next = work.checked_sub(1);
            *work = next.unwrap_or(0);
            next?;
            let parent = self.parents[id];
            if parent == id {
                return Some(id);
            }
            id = parent;
        }
    }
    fn union(&mut self, a: usize, b: usize, work: &mut usize) -> Option<bool> {
        let a = self.find(a, work)?;
        let b = self.find(b, work)?;
        if a == b {
            return Some(false);
        }
        self.parents[a.max(b)] = a.min(b);
        Some(true)
    }

    fn same(&mut self, a: usize, b: usize, work: &mut usize) -> Option<bool> {
        Some(self.find(a, work)? == self.find(b, work)?)
    }
}

fn transform(query: &Query, work: &mut usize) -> Option<Query> {
    let mut engine = Engine {
        work,
        variables: HashMap::new(),
        nodes: Vec::new(),
        ids: HashMap::new(),
        widths: Vec::new(),
        divisions: Vec::new(),
    };
    for (name, sort) in &query.variables {
        engine.pay(name.len().checked_add(1)?)?;
        engine.variables.insert(name.clone(), *sort);
    }
    let mut facts = Facts::default();
    for requirement in &query.requires {
        let id = engine.term(requirement, 0)?;
        engine.positive(id, &mut facts, 0)?;
    }
    let goal = engine.term(&query.goal, 0)?;
    let mut widths = BTreeSet::new();
    engine.goal_widths(goal, &mut widths, 0)?;
    if widths.is_empty() {
        return None;
    }
    engine.pay(widths.len().checked_add(1)?)?;
    engine.widths = widths.into_iter().collect();
    let goal = engine.boolean(goal, &facts, 0)?;
    engine.pay(engine.nodes.len().checked_add(1)?)?;
    let mut memo = vec![None; engine.nodes.len()];
    let goal = engine.emit(goal, &mut memo, 0)?;
    // Retain the original requires verbatim; no surrounding solver state or
    // ordinary mathematical hypothesis is imported into this query.
    engine.pay(query.requires.len().checked_add(query.variables.len())?)?;
    let mut requires = Vec::with_capacity(query.requires.len());
    for requirement in &query.requires {
        requires.push(copy(requirement, engine.work, 0)?);
    }
    let mut variables = Vec::with_capacity(query.variables.len());
    for (name, sort) in &query.variables {
        engine.pay(name.len().checked_add(1)?)?;
        variables.push((name.clone(), *sort));
    }
    Some(Query {
        variables,
        requires,
        goal,
        architecture: query.architecture,
    })
}

fn copy(term: &Term, work: &mut usize, depth: usize) -> Option<Term> {
    let next = work.checked_sub(1);
    *work = next.unwrap_or(0);
    next?;
    if depth > DEPTH {
        return None;
    }
    Some(match term {
        Term::Shared(inner) => Term::Shared(inner.clone()),
        Term::Euclidean(operation) => Term::Euclidean(operation.clone()),
        Term::Bool(value) => Term::Bool(*value),
        Term::Bits { value, width } => Term::Bits {
            value: *value,
            width: *width,
        },
        Term::Var(name) => {
            let next = work.checked_sub(name.len());
            *work = next.unwrap_or(0);
            next?;
            Term::Var(name.clone())
        }
        Term::App { op, args } => {
            let next = work.checked_sub(args.len());
            *work = next.unwrap_or(0);
            next?;
            let mut children = Vec::with_capacity(args.len());
            for arg in args {
                children.push(copy(arg, work, depth + 1)?);
            }
            Term::App {
                op: *op,
                args: children,
            }
        }
        Term::If { .. } | Term::Let { .. } | Term::Quant { .. } => return None,
    })
}

/// Return a semantics-preserving goal rewrite under only this query's facts.
/// Validation precedes traversal and checks the result. On unsupported shapes
/// or budget exhaustion `None` requires the caller to retain the original.
pub fn simplify(query: &Query) -> Option<Query> {
    query.validate().ok()?;
    let mut work = WORK;
    let result = transform(query, &mut work)?;
    result.validate().ok()?;
    Some(result)
}

#[cfg(test)]
mod tests;
