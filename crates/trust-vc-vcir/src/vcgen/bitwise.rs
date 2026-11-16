//! Ordinary-query bitwise semantics from the pinned prelude, separate from
//! the isolated BV prover: boxed Poly arguments, Int result, and range axioms
//! triggered by finite clips. No native BV definition is asserted here.

use super::term::{Sort, Term};
use super::val::range_bounds;
use crate::IntRange;

#[derive(Debug, Clone, Copy)]
pub(crate) enum Operation {
    Not,
    And,
    Or,
    Xor,
    LeftShift,
    RightShift,
}

impl Operation {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Not => "bit_not",
            Self::And => "bit_and",
            Self::Or => "bit_or",
            Self::Xor => "bit_xor",
            Self::LeftShift => "bit_shl",
            Self::RightShift => "bit_shr",
        }
    }
    pub(crate) fn arity(self) -> usize {
        if matches!(self, Self::Not) {
            1
        } else {
            2
        }
    }
}

fn unbox_argument(term: &Term) -> Option<&Term> {
    let Term::Call {
        name,
        args,
        sort: Sort::Poly,
    } = term
    else {
        return None;
    };
    (name == "box_int" && args.len() == 1 && args[0].sort() == Sort::Int).then(|| &args[0])
}

/// Ground instance of prelude_bit_{xor,or,and,shr}_{u,i}_inv. The actual
/// finite clip application is required, matching the pinned axiom's trigger.
pub(crate) fn range_fact(clip: &str, args: &[Term]) -> Option<Term> {
    let range = match clip {
        "clip_u8_oob" => IntRange::U(8),
        "clip_u16_oob" => IntRange::U(16),
        "clip_u32_oob" => IntRange::U(32),
        "clip_u64_oob" => IntRange::U(64),
        "clip_u128_oob" => IntRange::U(128),
        "clip_i8_oob" => IntRange::I(8),
        "clip_i16_oob" => IntRange::I(16),
        "clip_i32_oob" => IntRange::I(32),
        "clip_i64_oob" => IntRange::I(64),
        "clip_i128_oob" => IntRange::I(128),
        _ => return None,
    };
    let [result] = args else { return None };
    let Term::Call {
        name,
        args,
        sort: Sort::Int,
    } = result
    else {
        return None;
    };
    if args.len() != 2 || !matches!(name.as_str(), "bit_xor" | "bit_or" | "bit_and" | "bit_shr") {
        return None;
    }
    let left = unbox_argument(&args[0])?;
    let right = unbox_argument(&args[1])?;
    let (low, high) = range_bounds(range);
    let right_guard = if name == "bit_shr" {
        Term::le(Term::Int(0), right.clone())
    } else {
        right.clone().within_type_bounds(low, high)
    };
    Some(Term::implies(
        Term::and([left.clone().within_type_bounds(low, high), right_guard]),
        result.clone().within_type_bounds(low, high),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordinary_bounds_require_an_actual_clip_and_preserve_shift_sign_premise() {
        let boxed = |name| Term::call("box_int", vec![Term::var(name, Sort::Int)], Sort::Poly);
        let right = Term::var("count", Sort::Int);
        let raw = Term::call(
            "bit_shr",
            vec![
                boxed("left"),
                Term::call("box_int", vec![right.clone()], Sort::Poly),
            ],
            Sort::Int,
        );
        let fact = range_fact("clip_i8_oob", std::slice::from_ref(&raw)).unwrap();
        let (low, high) = range_bounds(IntRange::I(8));
        assert_eq!(
            fact,
            Term::implies(
                Term::and([
                    Term::var("left", Sort::Int).within_type_bounds(low, high),
                    Term::le(Term::Int(0), right)
                ]),
                raw.within_type_bounds(low, high)
            )
        );
        assert!(range_fact("user_clip_i8_oob", &[]).is_none());
        let shl = Term::call("bit_shl", vec![boxed("left"), boxed("right")], Sort::Int);
        assert!(range_fact("clip_i8_oob", &[shl]).is_none());
    }
}
