// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// ===========================================================================
// Contract 2: BV (Bitvector Theory)
// ===========================================================================

/// Bitvector operation kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum BvOp {
    Add,
    Sub,
    Mul,
    UDiv,
    URem,
    Shl,
    LShr,
    AShr,
    And,
    Or,
    Xor,
    Not,
    Neg,
    SignExt,
}

/// Contract trait for bitvector theory solver.
///
/// Captures the pre/postconditions of bitvector operations:
///
/// ```text
/// fn evaluate_bv_op(op: BvOp, lhs: u64, rhs: u64, width: u32) -> u64
///
/// requires:
///   width > 0 && width <= 64
///   lhs < 2^width
///   rhs < 2^width (for binary ops)
///
/// ensures |result|:
///   result < 2^width  (result fits in width bits)
///   // Specific semantics per operation (modular arithmetic, etc.)
/// ```
pub(crate) trait ContractBv {
    /// Evaluate a bitvector operation.
    fn evaluate_bv_op(&self, op: BvOp, lhs: u64, rhs: u64, width: u32) -> u64;
}

/// Mask for extracting low `width` bits.
#[must_use]
pub(crate) fn bv_mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

/// Check if bit `width-1` (the sign bit) is set.
#[must_use]
pub(crate) fn sign_bit_set(value: u64, width: u32) -> bool {
    if width == 0 || width > 64 {
        return false;
    }
    (value >> (width - 1)) & 1 == 1
}

/// Convert unsigned bitvector to signed i64 (sign-extend from width).
#[must_use]
pub(crate) fn to_signed(value: u64, width: u32) -> i64 {
    if width == 0 || width > 64 {
        return value as i64;
    }
    if sign_bit_set(value, width) {
        // Sign-extend: set all bits above width.
        let mask = bv_mask(width);
        (value | !mask) as i64
    } else {
        value as i64
    }
}

/// Reference BV implementation using standard Rust arithmetic with masking.
pub(crate) struct ReferenceBv;

impl ReferenceBv {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self
    }
}

impl ContractBv for ReferenceBv {
    fn evaluate_bv_op(&self, op: BvOp, lhs: u64, rhs: u64, width: u32) -> u64 {
        let mask = bv_mask(width);
        match op {
            BvOp::Add => lhs.wrapping_add(rhs) & mask,
            BvOp::Sub => lhs.wrapping_sub(rhs) & mask,
            BvOp::Mul => lhs.wrapping_mul(rhs) & mask,
            BvOp::UDiv => {
                // SMT-LIB: bvudiv by 0 = all-ones.
                lhs.checked_div(rhs).map_or(mask, |value| value & mask)
            }
            BvOp::URem => lhs
                .checked_rem(rhs)
                .map_or(lhs & mask, |value| value & mask),
            BvOp::Shl => {
                if rhs >= u64::from(width) {
                    0
                } else {
                    (lhs << rhs) & mask
                }
            }
            BvOp::LShr => {
                if rhs >= u64::from(width) {
                    0
                } else {
                    (lhs >> rhs) & mask
                }
            }
            BvOp::AShr => {
                if rhs >= u64::from(width) {
                    if sign_bit_set(lhs, width) {
                        mask
                    } else {
                        0
                    }
                } else {
                    let signed = to_signed(lhs, width);
                    let shifted = signed >> rhs;
                    (shifted as u64) & mask
                }
            }
            BvOp::And => (lhs & rhs) & mask,
            BvOp::Or => (lhs | rhs) & mask,
            BvOp::Xor => (lhs ^ rhs) & mask,
            BvOp::Not => (!lhs) & mask,
            BvOp::Neg => lhs.wrapping_neg() & mask,
            BvOp::SignExt => {
                // rhs = number of bits to extend by.
                // Result width = width + rhs (capped at 64).
                let new_width = (u64::from(width) + rhs).min(64) as u32;
                let new_mask = bv_mask(new_width);
                if sign_bit_set(lhs, width) {
                    let ext_bits = !bv_mask(width) & new_mask;
                    (lhs | ext_bits) & new_mask
                } else {
                    lhs & new_mask
                }
            }
        }
    }
}

/// Validates BV operation postconditions.
///
/// Checks:
/// 1. Result fits in `width` bits (result < 2^width).
/// 2. For shift operations: if shift amount >= width, result is 0 (logical)
///    or all-ones/0 (arithmetic).
/// 3. For sign extension: sign bit is preserved.
#[must_use]
pub(crate) fn validate_bv_postcondition(
    op: BvOp,
    lhs: u64,
    rhs: u64,
    width: u32,
    result: u64,
) -> bool {
    if width == 0 || width > 64 {
        return false;
    }

    let mask = bv_mask(width);

    // Postcondition 1: result fits in width bits (except SignExt which widens).
    if op != BvOp::SignExt && result > mask {
        return false;
    }

    // Postcondition 2: shift semantics.
    match op {
        BvOp::Shl | BvOp::LShr if rhs >= u64::from(width) && result != 0 => {
            return false;
        }
        BvOp::AShr if rhs >= u64::from(width) => {
            // Result should be all-ones or all-zeros depending on sign.
            let expected = if sign_bit_set(lhs, width) { mask } else { 0 };
            if result != expected {
                return false;
            }
        }
        _ => {}
    }

    // Postcondition 3: sign extension preserves sign bit.
    if op == BvOp::SignExt {
        let new_width = (u64::from(width) + rhs).min(64) as u32;
        let new_mask = bv_mask(new_width);
        if result > new_mask {
            return false;
        }
        // The original sign bit must be preserved in the extended value.
        let original_sign = sign_bit_set(lhs, width);
        let extended_sign = sign_bit_set(result, new_width);
        if original_sign != extended_sign {
            return false;
        }
    }

    true
}

/// Registers the BV evaluation contract as an extern_spec entry.
pub(crate) fn register_bv_evaluation_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_dpll::theory::bv::BvSolver::evaluate",
        &[
            "width > 0 && width <= 64".to_string(),
            "lhs < 2^width".to_string(),
            "rhs < 2^width".to_string(),
        ],
        &[
            "result < 2^width".to_string(),
            "op == Shl && rhs >= width ==> result == 0".to_string(),
            "op == SignExt ==> sign_preserved(lhs, result, width)".to_string(),
        ],
    );
}
