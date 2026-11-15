// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `trust_ir::Ty` -> the boundary sort trust-vc verifies over.
//!
//! The scalar fragment ONLY. Every other type declines by variant name, because
//! the alternative — approximating an unmodelled type with a scalar — is how a
//! verifier proves something about a value it never represented.

use super::Decline;
use crate::TrustSort;
use trust_ir::{Module, Ty};

/// Decodes trust-ir types against one module's target.
#[derive(Debug, Clone, Copy)]
pub(crate) struct TypeDecoder {
    /// Pointer width in BITS, from `Module.target_info.pointer_size` (bytes).
    ///
    /// `None` for a target-independent module: `Isize`/`Usize` then have no
    /// width and decline, exactly as `Ty::bit_width` returns `None` for them.
    /// Deliberately NOT defaulted to the host's `usize::BITS` — a proof that
    /// silently assumed 64-bit `usize` would be a proof about a different
    /// program on a 32-bit target.
    pointer_bits: Option<u32>,
}

impl TypeDecoder {
    pub(crate) fn from_module(module: &Module) -> Self {
        Self {
            pointer_bits: module.target_info.as_ref().and_then(|target| {
                match target.pointer_size {
                    2 => Some(16),
                    4 => Some(32),
                    8 => Some(64),
                    // Rust permits usize widths {16, 32, 64} only. Any other
                    // declared pointer size is a target trust-vc cannot reason
                    // about, so it is not a width at all.
                    _ => None,
                }
            }),
        }
    }

    /// Lower one trust-ir type, or decline naming the variant.
    pub(crate) fn sort(self, ty: &Ty) -> Result<TrustSort, Decline> {
        match ty {
            Ty::I8 => Ok(TrustSort::signed(8)),
            Ty::I16 => Ok(TrustSort::signed(16)),
            Ty::I32 => Ok(TrustSort::signed(32)),
            Ty::I64 => Ok(TrustSort::signed(64)),
            Ty::I128 => Ok(TrustSort::signed(128)),
            Ty::U8 => Ok(TrustSort::unsigned(8)),
            Ty::U16 => Ok(TrustSort::unsigned(16)),
            Ty::U32 => Ok(TrustSort::unsigned(32)),
            Ty::U64 => Ok(TrustSort::unsigned(64)),
            Ty::U128 => Ok(TrustSort::unsigned(128)),
            Ty::Isize => self
                .pointer_bits
                .map(TrustSort::signed)
                .ok_or_else(|| Decline::new(ISIZE_WITHOUT_TARGET)),
            Ty::Usize => self
                .pointer_bits
                .map(TrustSort::unsigned)
                .ok_or_else(|| Decline::new(USIZE_WITHOUT_TARGET)),
            Ty::Bool => Ok(TrustSort::Bool),
            Ty::Char => Ok(TrustSort::Char),
            other => Err(Decline::new(format!(
                "unmodelled trust-ir type `{}`: the discharge lane covers \
                 bool, char and the fixed-width integers only",
                variant_name(other)
            ))),
        }
    }
}

const ISIZE_WITHOUT_TARGET: &str =
    "unmodelled trust-ir type `Isize`: the module declares no usable target pointer size, \
     so the width is unknown (Rust permits 16, 32 or 64 bits)";
const USIZE_WITHOUT_TARGET: &str =
    "unmodelled trust-ir type `Usize`: the module declares no usable target pointer size, \
     so the width is unknown (Rust permits 16, 32 or 64 bits)";

/// The variant's spelling, for a decline message that names what was refused.
///
/// `Ty` is `#[non_exhaustive]` upstream, so the catch-all must produce SOMETHING
/// for a variant this build has never seen — "unknown" is still a decline.
fn variant_name(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "I8",
        Ty::I16 => "I16",
        Ty::I32 => "I32",
        Ty::I64 => "I64",
        Ty::I128 => "I128",
        Ty::U8 => "U8",
        Ty::U16 => "U16",
        Ty::U32 => "U32",
        Ty::U64 => "U64",
        Ty::U128 => "U128",
        Ty::Isize => "Isize",
        Ty::Usize => "Usize",
        Ty::Char => "Char",
        Ty::Bool => "Bool",
        // The producer-internal typing hole. Never wire-legal (the binary writer
        // and `validate_module` both reject it), but naming it beats "unknown".
        Ty::Error => "Error",
        Ty::F16 => "F16",
        Ty::F32 => "F32",
        Ty::F64 => "F64",
        Ty::Vector(..) => "Vector",
        Ty::Ptr => "Ptr",
        Ty::FatPtr(_) => "FatPtr",
        Ty::Unit => "Unit",
        Ty::Never => "Never",
        Ty::Struct(_) => "Struct",
        Ty::Array(..) => "Array",
        Ty::Tuple(_) => "Tuple",
        Ty::Enum(_) => "Enum",
        Ty::Func(_) => "Func",
        // Shared references are NOT erased to their referent here. Erasure is
        // only sound with the encoder's erased-shared-ref marking, which the
        // unit boundary does not carry, and the body lane declines `Load`
        // through a pointer anyway — so erasing would buy nothing and would
        // silently equate `&T` with `T` at the unit surface.
        Ty::Ref(_) => "Ref",
        Ty::RefMut(_) => "RefMut",
        Ty::PtrConst(_) => "PtrConst",
        Ty::PtrMut(_) => "PtrMut",
        Ty::Rc(_) => "Rc",
        Ty::Set(..) => "Set",
        Ty::Sequence(_) => "Sequence",
        Ty::Record(_) => "Record",
        Ty::Closure(_) => "Closure",
        Ty::Refine(..) => "Refine",
        Ty::Dialect(_) => "Dialect",
        Ty::Storage(_) => "Storage",
        // trust-ir v67's tensor. The name reads neither the element nor the
        // rank.
        Ty::Tensor(..) => "Tensor",
        #[allow(unreachable_patterns)]
        _ => "unknown",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Endianness, StructPassingPolicy, TargetInfo, TyId};

    fn module_with_pointer_size(pointer_size: u32) -> Module {
        let mut module = Module::new("scalar_fragment");
        module.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
        module
    }

    #[test]
    fn lowers_the_scalar_fragment() {
        let module = module_with_pointer_size(8);
        let decoder = TypeDecoder::from_module(&module);
        assert_eq!(decoder.sort(&Ty::Bool), Ok(TrustSort::Bool));
        assert_eq!(decoder.sort(&Ty::Char), Ok(TrustSort::Char));
        assert_eq!(decoder.sort(&Ty::I8), Ok(TrustSort::signed(8)));
        assert_eq!(decoder.sort(&Ty::U128), Ok(TrustSort::unsigned(128)));
        assert_eq!(decoder.sort(&Ty::Usize), Ok(TrustSort::unsigned(64)));
        assert_eq!(decoder.sort(&Ty::Isize), Ok(TrustSort::signed(64)));
    }

    /// `usize` is the target's width, never the host's. A 32-bit module must not
    /// borrow this machine's 64 bits: that would prove a property of a program
    /// that was never compiled.
    #[test]
    fn usize_follows_the_modules_target_not_the_host() {
        let module = module_with_pointer_size(4);
        let decoder = TypeDecoder::from_module(&module);
        assert_eq!(decoder.sort(&Ty::Usize), Ok(TrustSort::unsigned(32)));
        assert_eq!(decoder.sort(&Ty::Isize), Ok(TrustSort::signed(32)));
    }

    #[test]
    fn usize_declines_without_a_declared_target() {
        let decoder = TypeDecoder::from_module(&Module::new("target_independent"));
        let decline = decoder.sort(&Ty::Usize).expect_err("no target, no width");
        assert!(decline.reason().contains("Usize"), "{decline}");
        assert!(decline.reason().contains("pointer size"), "{decline}");
        // A width Rust never uses is not a width.
        let odd = TypeDecoder::from_module(&module_with_pointer_size(3));
        assert!(odd.sort(&Ty::Usize).is_err());
    }

    /// Every type outside the fragment declines BY NAME. The list is the
    /// fail-closed surface, so it is asserted rather than described.
    #[test]
    fn every_unmodelled_type_declines_naming_itself() {
        let module = module_with_pointer_size(8);
        let decoder = TypeDecoder::from_module(&module);
        for (ty, name) in [
            (Ty::Unit, "Unit"),
            (Ty::Never, "Never"),
            (Ty::F32, "F32"),
            (Ty::F64, "F64"),
            (Ty::Ptr, "Ptr"),
            (Ty::Ref(Box::new(Ty::U64)), "Ref"),
            (Ty::RefMut(Box::new(Ty::U64)), "RefMut"),
            (Ty::PtrConst(Box::new(Ty::U64)), "PtrConst"),
            (Ty::PtrMut(Box::new(Ty::U64)), "PtrMut"),
            (Ty::Rc(Box::new(Ty::U64)), "Rc"),
            (Ty::Tuple(vec![Ty::U64, Ty::Bool]), "Tuple"),
            (Ty::Array(TyId::new(0), 4), "Array"),
            (Ty::Sequence(TyId::new(0)), "Sequence"),
            (Ty::Vector(Box::new(Ty::U64), 4), "Vector"),
            (Ty::Error, "Error"),
            (Ty::Storage(trust_ir::StorageLayout::new(80, 8)), "Storage"),
            // trust-ir v67: a tensor declines by name at every rank and
            // element, scalar-shaped rank 0 included.
            (Ty::Tensor(Box::new(Ty::I32), 2), "Tensor"),
            (Ty::Tensor(Box::new(Ty::U8), 0), "Tensor"),
        ] {
            let decline = decoder
                .sort(&ty)
                .expect_err("type is outside the scalar fragment");
            assert!(
                decline.reason().contains(name),
                "decline for {name} must name it, got: {decline}"
            );
        }
    }
}
