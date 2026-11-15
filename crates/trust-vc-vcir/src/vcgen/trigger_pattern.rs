//! Typed trigger heads retain the original ordinary scalar AST. Clip metadata
//! is minted by spec::clip_pattern; no query/Core clipping ABI is changed.
use super::spec;
use super::term::{ArithOp, Sort, Term};
use crate::IntRange;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Head {
    Call,
    Arithmetic(ArithOp),
    Clip(IntRange),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Pattern {
    term: Term,
    head: Head,
}

impl Pattern {
    /// The current result of an actual finite integer clipping operation,
    /// lowered by `Tr::leaf` with the same operator/type rules as its body.
    /// This retains that WHOLE term; it does not reconstruct an operation or
    /// accept a raw ITE through `application`. The existing metered template
    /// admission must still validate the complete clip ABI before use.
    pub(super) fn lowered_finite_clip(term: Term, range: IntRange) -> Option<Self> {
        if term.sort() != Sort::Int || !spec::CLIP_RANGES.contains(&range) {
            return None;
        }
        Some(Self {
            term,
            head: Head::Clip(range),
        })
    }

    pub(super) fn application(term: Term) -> Option<Self> {
        let head = match &term {
            Term::Call { .. } => Head::Call,
            Term::Arith(op, left, right)
                if left.sort() == Sort::Int && right.sort() == Sort::Int =>
            {
                Head::Arithmetic(*op)
            }
            _ => return None,
        };
        Some(Self { term, head })
    }
    pub(super) fn clipped(value: spec::ClipPattern) -> Self {
        let (range, term) = value.into_parts();
        Self {
            term,
            head: Head::Clip(range),
        }
    }
    pub(super) fn term(&self) -> &Term {
        &self.term
    }
    pub(super) fn head(&self) -> Head {
        self.head
    }
    pub(super) fn substitute(&self, values: &HashMap<&str, Term>) -> Self {
        Self {
            term: self.term.substitute(values),
            head: self.head,
        }
    }
    pub(super) fn valid_head(&self, pay: &mut impl FnMut(usize) -> bool) -> bool {
        if !pay(1) {
            return false;
        }
        match (self.head, &self.term) {
            (Head::Call, Term::Call { .. }) => true,
            (Head::Arithmetic(expected), Term::Arith(op, a, b)) => {
                *op == expected && a.sort() == Sort::Int && b.sort() == Sort::Int
            }
            (Head::Clip(range), _) => spec::clip_fallback(&self.term, range, pay).is_some(),
            _ => false,
        }
    }
}

/// One checked substitution/matching path for plain call/arithmetic terms and
/// private source-minted clip descriptors. A plain ITE never acquires Clip
/// metadata through this trait; its root is unsupported.
pub(super) trait Template: Clone {
    fn term(&self) -> &Term;
    fn substitute(&self, values: &HashMap<&str, Term>) -> Self;
    fn root(&self) -> Option<Head>;
    fn valid_head(&self, pay: &mut impl FnMut(usize) -> bool) -> bool;
}

impl Template for Pattern {
    fn term(&self) -> &Term {
        Pattern::term(self)
    }
    fn substitute(&self, values: &HashMap<&str, Term>) -> Self {
        Pattern::substitute(self, values)
    }
    fn root(&self) -> Option<Head> {
        Some(self.head())
    }
    fn valid_head(&self, pay: &mut impl FnMut(usize) -> bool) -> bool {
        Pattern::valid_head(self, pay)
    }
}

impl Template for Term {
    fn term(&self) -> &Term {
        self
    }
    fn substitute(&self, values: &HashMap<&str, Term>) -> Self {
        Term::substitute(self, values)
    }
    fn root(&self) -> Option<Head> {
        match self {
            Term::Call { .. } => Some(Head::Call),
            Term::Arith(op, a, b) if a.sort() == Sort::Int && b.sort() == Sort::Int => {
                Some(Head::Arithmetic(*op))
            }
            _ => None,
        }
    }
    fn valid_head(&self, pay: &mut impl FnMut(usize) -> bool) -> bool {
        pay(1) && self.root().is_some()
    }
}

#[cfg(test)]
#[path = "trigger_pattern_tests.rs"]
mod tests;
