//! Term-keyed BV width metadata whose SIGNEDNESS can no longer be borrowed
//! from a different occurrence of the same term.
//!
//! ay hash-conses terms: the literal `u64::MAX` and the `i64` literal `-1` are
//! ONE BV64 term, as are `200u8` / `-56i8` and `255u8` / `-1i8`. A plain
//! `HashMap<Term, (width, signed)>` therefore cannot represent "this occurrence
//! is unsigned, that one is signed": every re-encoding of the shared term
//! overwrote the entry, and whichever occurrence was encoded LAST decided the
//! signedness every other occurrence was lifted, extended and compared with.
//! Measured consequence: `u64::MAX < a.len() + (-1i64)` came back `Verified`
//! (the right operand's `-1` re-registered the term as signed, and the left
//! operand was then lifted to Int as `-1`).
//!
//! The encoder's rule is now that signedness is a property of the OPERAND —
//! its IR type at the use site (`width_coercion::ir_type_signedness`) — and the
//! comparison, arithmetic, bitwise, shift, wrapping, ITE and match encoders
//! take it from there. This table remains for the use sites that hold no IR
//! type for the term they coerce (collection element / key / length
//! plumbing), and for them it is made unable to hand out a WRONG sign:
//!
//! * the width is the term's own (a BV term has exactly one width), so
//!   [`TermWidths::width`] answers whatever the entry says;
//! * a signedness is answered only while every registration of the term
//!   AGREED on it. The first disagreeing registration marks the entry
//!   CONTESTED for the rest of the encoding, and [`TermWidths::get`] then
//!   answers `None` — the caller's "no metadata" path, which leaves the term
//!   uncoerced, so a width mismatch surfaces as a solver sort error (`Unknown`)
//!   instead of a silently mis-signed value;
//! * a constant whose top bit is clear denotes the same integer under both
//!   interpretations, so the literal encoders register it SIGN-NEUTRAL
//!   ([`TermWidths::insert_sign_neutral`]) and it is never contested — `0u8`
//!   and `0i8` both being in play costs nothing.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use ay_dpll::api::Term;

/// What the registrations of one term say about its signedness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SignFact {
    /// Every registration so far agreed; the tuple's `bool` is the answer.
    Agreed,
    /// A constant with its top bit clear: both interpretations denote the same
    /// integer, so no pair of registrations can disagree about its VALUE.
    Neutral,
    /// Two registrations disagreed. Never answered again.
    Contested,
}

#[derive(Debug, Clone)]
struct Entry {
    info: (u32, bool),
    sign: SignFact,
}

/// BV width/signedness metadata keyed by term; see the module doc.
#[derive(Debug, Clone, Default)]
pub(crate) struct TermWidths {
    entries: HashMap<Term, Entry>,
}

impl TermWidths {
    /// An empty table.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record `(width, signed)` for one occurrence of `term`.
    ///
    /// The width is overwritten (last writer), exactly as before. The sign is
    /// kept only while it agrees with every earlier registration; a
    /// disagreement contests the entry permanently (a sign-neutral constant is
    /// exempt — it has no sign to disagree about).
    pub(crate) fn insert(&mut self, term: Term, info: (u32, bool)) {
        match self.entries.get_mut(&term) {
            None => {
                self.entries.insert(
                    term,
                    Entry {
                        info,
                        sign: SignFact::Agreed,
                    },
                );
            }
            Some(entry) => {
                let sign = match entry.sign {
                    SignFact::Agreed if entry.info.1 != info.1 => SignFact::Contested,
                    other => other,
                };
                entry.info = info;
                entry.sign = sign;
            }
        }
    }

    /// Record a CONSTANT whose top bit (at `info.0`) is clear, so it denotes
    /// the same integer read signed or unsigned. It is never contested.
    pub(crate) fn insert_sign_neutral(&mut self, term: Term, info: (u32, bool)) {
        self.entries.insert(
            term,
            Entry {
                info,
                sign: SignFact::Neutral,
            },
        );
    }

    /// `(width, signed)` for `term` — `None` when it was never registered OR
    /// when its registrations disagreed on the sign (see the module doc).
    pub(crate) fn get(&self, term: &Term) -> Option<&(u32, bool)> {
        self.entries
            .get(term)
            .filter(|entry| entry.sign != SignFact::Contested)
            .map(|entry| &entry.info)
    }

    /// The registered width of `term`, whether or not its sign is contested.
    pub(crate) fn width(&self, term: &Term) -> Option<u32> {
        self.entries.get(term).map(|entry| entry.info.0)
    }

    /// Whether the registrations of `term` disagreed on its signedness.
    pub(crate) fn is_sign_contested(&self, term: &Term) -> bool {
        self.entries
            .get(term)
            .is_some_and(|entry| entry.sign == SignFact::Contested)
    }

    /// Drop the entry for a term that stopped being a BV (an Int lift).
    ///
    /// A CONTESTED entry is kept: forgetting it would let the next
    /// registration of the same term be believed again.
    pub(crate) fn remove(&mut self, term: &Term) -> Option<(u32, bool)> {
        if self.is_sign_contested(term) {
            return None;
        }
        self.entries.remove(term).map(|entry| entry.info)
    }

    /// Whether `term` has any entry (contested or not).
    #[cfg(test)]
    pub(crate) fn contains_key(&self, term: &Term) -> bool {
        self.entries.contains_key(term)
    }

    /// Whether no term is registered.
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
impl std::ops::Index<&Term> for TermWidths {
    type Output = (u32, bool);

    /// Test convenience mirroring `HashMap` indexing: the uncontested entry.
    fn index(&self, term: &Term) -> &Self::Output {
        match self.get(term) {
            Some(info) => info,
            None => panic!("no uncontested term_widths entry for {term:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::TermWidths;
    use ay_dpll::api::{Logic, Solver, Sort};

    fn terms() -> (Solver, ay_dpll::api::Term, ay_dpll::api::Term) {
        let mut solver = Solver::try_new(Logic::All).expect("solver");
        let x = solver.declare_const("x", Sort::bitvec(8));
        let y = solver.declare_const("y", Sort::bitvec(8));
        (solver, x, y)
    }

    #[test]
    fn agreeing_registrations_are_answered() {
        let (_solver, x, _) = terms();
        let mut widths = TermWidths::new();
        widths.insert(x, (8, true));
        widths.insert(x, (8, true));
        assert_eq!(widths.get(&x), Some(&(8, true)));
    }

    #[test]
    fn a_disagreeing_registration_contests_the_sign_for_good() {
        let (_solver, x, _) = terms();
        let mut widths = TermWidths::new();
        widths.insert(x, (8, false));
        widths.insert(x, (8, true));
        assert_eq!(widths.get(&x), None, "last writer must not win");
        assert!(widths.is_sign_contested(&x));
        assert_eq!(widths.width(&x), Some(8), "the width is still known");
        widths.insert(x, (8, false));
        assert_eq!(widths.get(&x), None, "a contest is never forgotten");
        assert_eq!(widths.remove(&x), None, "nor removed");
        assert!(widths.is_sign_contested(&x));
    }

    #[test]
    fn a_sign_neutral_constant_is_never_contested() {
        let (_solver, x, _) = terms();
        let mut widths = TermWidths::new();
        widths.insert_sign_neutral(x, (8, false));
        widths.insert(x, (8, true));
        widths.insert(x, (8, false));
        assert!(widths.get(&x).is_some());
        assert!(!widths.is_sign_contested(&x));
    }
}
