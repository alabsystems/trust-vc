//! Lossless integer-to-BV construction following the pinned BV translator.
//!
//! Signedness tracks mathematical interpretation; the underlying SMT sort
//! remains a width alone. Arithmetic first chooses enough bits for the exact
//! mathematical result. Explicit finite casts then clip/reinterpret it.

use crate::{IntLit, Op, Term, MAX_WIDTH};
use std::sync::Arc;

/// A BV expression together with its mathematical integer interpretation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Integer {
    term: Term,
    width: u32,
    signed: bool,
    /// The elaborated root is an unsigned addition/multiplication. The
    /// pinned translator admits an explicit nat clip at exactly this root.
    nat_arithmetic: bool,
}

/// A guarded construction of exact Euclidean arithmetic. The ordinary BV
/// expansion, including its caller-supplied zero arm, defines its semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Euclidean {
    numerator: Integer,
    denominator: Integer,
    remainder: bool,
    width: u32,
    signed: bool,
    expanded: Term,
}

impl Euclidean {
    /// Encode the same guarded finite expression as for any other BV term.
    pub fn expanded(&self) -> &Term {
        &self.expanded
    }

    pub(crate) fn operands(&self) -> [(&Term, u32, bool); 2] {
        [&self.numerator, &self.denominator].map(|value| (&value.term, value.width, value.signed))
    }

    pub(crate) fn result(&self) -> (u32, bool) {
        (self.width, self.signed)
    }

    pub(crate) fn is_remainder(&self) -> bool {
        self.remainder
    }
}

/// Mathematical arithmetic, including Euclidean division/remainder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arithmetic {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

/// Mathematical comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Comparison {
    Eq,
    Lt,
    Le,
}

fn shared(term: Term) -> Term {
    if matches!(&term, Term::Shared(_) | Term::Euclidean(_)) {
        term
    } else {
        Term::Shared(std::sync::Arc::new(term))
    }
}
fn unary(op: Op, term: Term) -> Term {
    shared(Term::App {
        op,
        args: vec![term],
    })
}
fn binary(op: Op, left: Term, right: Term) -> Term {
    shared(Term::App {
        op,
        args: vec![left, right],
    })
}
fn condition(condition: Term, then_term: Term, else_term: Term) -> Term {
    shared(Term::If {
        condition: Box::new(condition),
        then_term: Box::new(then_term),
        else_term: Box::new(else_term),
    })
}
fn width(width: u32) -> Result<u32, &'static str> {
    if width == 0 || width > MAX_WIDTH {
        Err("isolated integer BV width exhausted")
    } else {
        Ok(width)
    }
}
fn add_width(left: u32, right: u32) -> Result<u32, &'static str> {
    width(
        left.checked_add(right)
            .ok_or("isolated integer BV width overflow")?,
    )
}

impl Integer {
    /// A source variable/binder or another already typed BV term. The final
    /// query still checks that its declared native sort is exactly this width.
    pub fn from_bits(term: Term, bits: u32, signed: bool) -> Result<Self, &'static str> {
        Ok(Self {
            term: shared(term),
            width: width(bits)?,
            signed,
            nat_arithmetic: false,
        })
    }

    /// The minimal exact finite representation of an integer literal.
    pub fn literal(value: IntLit) -> Self {
        let (bits, signed) = if value.negative && value.magnitude != 0 {
            (129 - (value.magnitude - 1).leading_zeros(), true)
        } else {
            ((128 - value.magnitude.leading_zeros()).max(1), false)
        };
        Self {
            term: shared(Term::Bits { value, width: bits }),
            width: bits,
            signed,
            nat_arithmetic: false,
        }
    }

    /// Mathematical interpretation of this expression.
    pub fn is_signed(&self) -> bool {
        self.signed
    }
    /// Native BV width.
    pub fn bits(&self) -> u32 {
        self.width
    }
    /// This is elaboration shape metadata, not a nonnegative assumption.
    pub fn permits_nat_clip(&self) -> bool {
        self.nat_arithmetic
    }
    /// Remove the accepted nonnegative arithmetic clip without adding a
    /// premise; a subsequent clip sees the resulting cast, not the old root.
    pub fn clip_nat(mut self) -> Result<Self, &'static str> {
        if !self.nat_arithmetic {
            return Err("not supported: nat cast here");
        }
        self.nat_arithmetic = false;
        Ok(self)
    }
    /// The explicit BV term.
    pub fn into_term(self) -> Term {
        self.term
    }

    fn zero(bits: u32) -> Term {
        Term::Bits {
            value: IntLit {
                negative: false,
                magnitude: 0,
            },
            width: bits,
        }
    }
    fn one(bits: u32) -> Term {
        Term::Bits {
            value: IntLit {
                negative: false,
                magnitude: 1,
            },
            width: bits,
        }
    }

    fn resize(self, target: u32) -> Result<Self, &'static str> {
        width(target)?;
        let term = if target == self.width {
            self.term
        } else if target < self.width {
            unary(
                Op::Extract {
                    high: target - 1,
                    low: 0,
                },
                self.term,
            )
        } else {
            unary(
                if self.signed {
                    Op::SignExtend(target - self.width)
                } else {
                    Op::ZeroExtend(target - self.width)
                },
                self.term,
            )
        };
        Ok(Self {
            term,
            width: target,
            signed: self.signed,
            nat_arithmetic: self.nat_arithmetic,
        })
    }

    /// A finite `as` cast. For a widening cast the pinned translator retains
    /// a smaller lossless representation, except signed-to-unsigned needs the
    /// full target width to represent its modular result.
    pub fn clip(mut self, target: u32, signed: bool) -> Result<Self, &'static str> {
        width(target)?;
        self.nat_arithmetic = false;
        if target > self.width && !(self.signed && !signed) {
            return Ok(self);
        }
        let mut result = self.resize(target)?;
        result.signed = signed;
        Ok(result)
    }

    fn align(self, other: Self) -> Result<(Self, Self), &'static str> {
        let left = if !self.signed && other.signed {
            add_width(self.width, 1)?
        } else {
            self.width
        };
        let right = if self.signed && !other.signed {
            add_width(other.width, 1)?
        } else {
            other.width
        };
        let target = left.max(right);
        let signed = self.signed || other.signed;
        let mut left = self.resize(target)?;
        let mut right = other.resize(target)?;
        left.signed = signed;
        right.signed = signed;
        Ok((left, right))
    }

    /// Exact mathematical comparison, including mixed signed/unsigned values.
    pub fn compare(self, other: Self, comparison: Comparison) -> Result<Term, &'static str> {
        let (left, right) = self.align(other)?;
        let op = match comparison {
            Comparison::Eq => Op::Eq,
            Comparison::Lt => {
                if left.signed {
                    Op::SLt
                } else {
                    Op::ULt
                }
            }
            Comparison::Le => {
                if left.signed {
                    Op::SLe
                } else {
                    Op::ULe
                }
            }
        };
        Ok(binary(op, left.term, right.term))
    }

    /// An exact finite conditional; branch values are aligned losslessly.
    pub fn conditional(test: Term, yes: Self, no: Self) -> Result<Self, &'static str> {
        let (yes, no) = yes.align(no)?;
        Ok(Self {
            term: condition(test, yes.term, no.term),
            width: yes.width,
            signed: yes.signed,
            nat_arithmetic: false,
        })
    }

    /// Mathematical bitwise not, or an explicitly width-clipped bitwise not.
    pub fn bit_not(self, clipped_width: Option<u32>) -> Result<Self, &'static str> {
        let mut value = if let Some(bits) = clipped_width {
            self.resize(bits)?
        } else if self.signed {
            self
        } else {
            let bits = add_width(self.width, 1)?;
            self.resize(bits)?
        };
        value.term = unary(Op::BitNot, value.term);
        value.signed = clipped_width.is_none();
        value.nat_arithmetic = false;
        Ok(value)
    }

    /// Exact bitwise `and`, `or`, or `xor`, with mathematical sign extension.
    pub fn bitwise(self, other: Self, op: Op) -> Result<Self, &'static str> {
        if !matches!(op, Op::BitAnd | Op::BitOr | Op::BitXor) {
            return Err("not an integer bitwise operator");
        }
        let (left, right) = self.align(other)?;
        Ok(Self {
            term: binary(op, left.term, right.term),
            width: left.width,
            signed: left.signed,
            nat_arithmetic: false,
        })
    }

    /// Exact `+ - *` with enough bits for every mathematical result. Division
    /// and remainder require [`Self::euclidean`] so zero is explicitly guarded.
    pub fn arithmetic(self, other: Self, op: Arithmetic) -> Result<Self, &'static str> {
        let nat_arithmetic =
            !self.signed && !other.signed && matches!(op, Arithmetic::Add | Arithmetic::Mul);
        let (bits, signed, native) = match op {
            Arithmetic::Add | Arithmetic::Sub => {
                let subtraction = op == Arithmetic::Sub;
                let left_extra = if !self.signed && other.signed { 2 } else { 1 };
                let right_extra = if self.signed && !other.signed { 2 } else { 1 };
                (
                    add_width(self.width, left_extra)?.max(add_width(other.width, right_extra)?),
                    self.signed || other.signed || subtraction,
                    if subtraction { Op::Sub } else { Op::Add },
                )
            }
            Arithmetic::Mul => (
                add_width(self.width, other.width)?,
                self.signed || other.signed,
                Op::Mul,
            ),
            Arithmetic::Div | Arithmetic::Rem => {
                return Err("division needs an explicit arbitrary zero case")
            }
        };
        let left = self.resize(bits)?;
        let right = other.resize(bits)?;
        Ok(Self {
            term: binary(native, left.term, right.term),
            width: bits,
            signed,
            nat_arithmetic,
        })
    }

    /// Euclidean integer `/` or `%`. `arbitrary` supplies a fresh independent
    /// value of the returned width ONLY for the zero-divisor case. It must be
    /// declared in the isolated query; no enclosing hypotheses define it.
    pub fn euclidean(
        self,
        other: Self,
        remainder: bool,
        arbitrary: Term,
    ) -> Result<Self, &'static str> {
        let numerator = self.clone();
        let denominator = other.clone();
        let (left, right) = self.align(other)?;
        let bits = left.width;
        let signed = left.signed;
        let denominator_zero = binary(Op::Eq, right.term.clone(), Self::zero(bits));
        let (term, output_bits) = if !left.signed {
            (
                binary(
                    if remainder { Op::URem } else { Op::UDiv },
                    left.term,
                    right.term,
                ),
                bits,
            )
        } else if remainder {
            let native = binary(Op::SRem, left.term, right.term.clone());
            let negative_denominator = binary(Op::SLt, right.term.clone(), Self::zero(bits));
            let absolute = condition(
                negative_denominator,
                binary(Op::Sub, Self::zero(bits), right.term.clone()),
                right.term,
            );
            let negative_remainder = binary(Op::SLt, native.clone(), Self::zero(bits));
            (
                condition(
                    negative_remainder,
                    binary(Op::Add, native.clone(), absolute),
                    native,
                ),
                bits,
            )
        } else {
            let bits = add_width(bits, 1)?;
            let left = left.resize(bits)?;
            let right = right.resize(bits)?;
            let quotient = binary(Op::SDiv, left.term.clone(), right.term.clone());
            let native_remainder = binary(Op::SRem, left.term, right.term.clone());
            let negative_remainder = binary(Op::SLt, native_remainder, Self::zero(bits));
            let positive_denominator = binary(Op::SLt, Self::zero(bits), right.term);
            let corrected = condition(
                positive_denominator,
                binary(Op::Sub, quotient.clone(), Self::one(bits)),
                binary(Op::Add, quotient.clone(), Self::one(bits)),
            );
            (condition(negative_remainder, corrected, quotient), bits)
        };
        Ok(Self {
            term: Term::Euclidean(Arc::new(Euclidean {
                numerator,
                denominator,
                remainder,
                width: output_bits,
                signed,
                expanded: Term::If {
                    condition: Box::new(denominator_zero),
                    then_term: Box::new(arbitrary),
                    else_term: Box::new(term),
                },
            })),
            width: output_bits,
            signed,
            nat_arithmetic: false,
        })
    }

    /// Right shift: signed counts are unsupported by the pinned translator.
    /// A count wider than the value is kept, so it cannot wrap modulo width.
    pub fn shift_right(self, amount: Self) -> Result<Self, &'static str> {
        if amount.signed {
            return Err("a signed bit-vector shift count");
        }
        let original_width = self.width;
        let signed = self.signed;
        let target = self.width.max(amount.width);
        let left = self.resize(target)?;
        let right = amount.resize(target)?;
        Self {
            term: binary(
                if signed { Op::AShr } else { Op::LShr },
                left.term,
                right.term,
            ),
            width: target,
            signed,
            nat_arithmetic: false,
        }
        .resize(original_width)
    }

    /// Width-clipped left shift, preserving a wide count before truncation.
    pub fn shift_left(
        self,
        amount: Self,
        output_width: u32,
        signed: bool,
    ) -> Result<Self, &'static str> {
        if amount.signed {
            return Err("a signed bit-vector shift count");
        }
        width(output_width)?;
        let target = output_width.max(amount.width);
        let left = self.resize(target)?;
        let right = amount.resize(target)?;
        let mut result = Self {
            term: binary(Op::Shl, left.term, right.term),
            width: target,
            signed,
            nat_arithmetic: false,
        }
        .resize(output_width)?;
        result.signed = signed;
        Ok(result)
    }
}
