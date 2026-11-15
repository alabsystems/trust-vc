//! The Verus marker items the reader recognizes.
//!
//! Upstream's `verus_builtin` crate tags every marker function, trait method
//! and type with `#[rustc_diagnostic_item = "verus::verus_builtin::<name>"]`.
//! The reader asks rustc for the crate graph's diagnostic items, keeps the
//! ones whose name starts with `verus::`, and matches a resolved callee or type
//! by its `DefId` against that table. A user function that happens to be
//! called `requires` therefore never looks like a marker: only the definition
//! that carries the diagnostic item does.
//!
//! This module is the rustc-free half: the mapping from diagnostic-item names
//! to [`VerusItem`]. Names under `verus::` that the reader does not handle map
//! to [`VerusItem::Other`], so a use of one is refused by name instead of being
//! mistaken for an ordinary function.

/// Prefix of every diagnostic item the reader treats as a Verus item.
pub const VERUS_PREFIX: &str = "verus::";

/// Prefix of the items defined by `verus_builtin`.
const BUILTIN_PREFIX: &str = "verus::verus_builtin::";

/// Comparison operators of the `SpecOrd` trait.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OrdOp {
    /// `spec_lt`.
    Lt,
    /// `spec_le`.
    Le,
    /// `spec_gt`.
    Gt,
    /// `spec_ge`.
    Ge,
}

/// Arithmetic of the `Spec*` traits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpecArith {
    /// `SpecAdd::spec_add`.
    Add,
    /// `SpecSub::spec_sub`.
    Sub,
    /// `SpecMul::spec_mul`.
    Mul,
    /// `SpecEuclideanOrRealDiv::spec_euclidean_or_real_div`.
    Div,
    /// `SpecEuclideanMod::spec_euclidean_mod`.
    Mod,
}

/// Bitwise operators of the `Spec*` traits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpecBitwise {
    /// `SpecBitAnd::spec_bitand`.
    And,
    /// `SpecBitOr::spec_bitor`.
    Or,
    /// `SpecBitXor::spec_bitxor`.
    Xor,
    /// `SpecShl::spec_shl`.
    Shl,
    /// `SpecShr::spec_shr`.
    Shr,
}

/// The parts of a chained comparison (`a <= b < c`), which `verus!`
/// writes as `spec_chained_cmp(spec_chained_lt(spec_chained_le(
/// spec_chained_value(a), b), c))`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChainOp {
    /// `spec_chained_value`: the first element.
    Value,
    /// `spec_chained_le`.
    Le,
    /// `spec_chained_lt`.
    Lt,
    /// `spec_chained_ge`.
    Ge,
    /// `spec_chained_gt`.
    Gt,
    /// `spec_chained_eq`.
    Eq,
    /// `spec_chained_cmp`: the whole chain as a `bool`.
    Cmp,
}

/// The builtin functions `add`, `sub` and `mul`: arithmetic that keeps the
/// operand type (wrapping in ghost code, checked in exec code).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BuiltinArith {
    /// `add`.
    Add,
    /// `sub`.
    Sub,
    /// `mul`.
    Mul,
}

/// A Verus item, identified by its diagnostic-item name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VerusItem {
    /// Native architecture-width builtin; no host width is substituted.
    ArchWordBits,
    /// Only the checked local global-size directive may consume this item.
    GlobalSizeOf,
    /// `requires`: a header call holding the preconditions.
    Requires,
    /// `ensures`: a header call holding the postconditions.
    Ensures,
    /// `recommends`: a header call holding the recommendations.
    Recommends,
    /// A header marker the reader does not handle yet (`decreases`,
    /// `returns`, `opens_invariants`, `no_unwind_when`, loop invariants,
    /// ...).
    OtherHeader,
    /// `opens_invariants_none`: the function opens no invariant.
    OpensInvariantsNone,
    /// `no_unwind`: the function does not unwind.
    NoUnwind,
    /// `assert_`.
    Assert,
    /// `assume_`.
    Assume,
    /// `admit`.
    Admit,
    /// `reveal_hide_`: reveal (fuel 1 or more) or hide (fuel 0) a spec
    /// function.
    RevealHide,
    /// `reveal_hide_internal_path_`: names the function inside a reveal.
    RevealHideInternalPath,
    /// `imply`: `==>`.
    Imply,
    /// `spec_eq`: spec `==`.
    SpecEq,
    /// `equal`: spec equality as a function.
    Equal,
    /// `SpecOrd` comparisons.
    SpecOrd(OrdOp),
    /// `Spec*` arithmetic.
    SpecArith(SpecArith),
    /// `SpecNeg::spec_neg`.
    SpecNeg,
    /// `Spec*` bitwise operators.
    SpecBitwise(SpecBitwise),
    /// The builtin `add`, `sub` and `mul` functions.
    BuiltinArith(BuiltinArith),
    /// `spec_literal_integer`: a literal of any integer type.
    SpecLiteralInteger,
    /// `spec_literal_int`: an `int` literal.
    SpecLiteralInt,
    /// `spec_literal_nat`: a `nat` literal.
    SpecLiteralNat,
    /// `spec_cast_integer`: spec `as` between integer types.
    SpecCastInteger,
    /// `old`: the entry value behind a `&mut` parameter.
    Old,
    /// `get_variant_field`: a checked, spec-only native field read.
    GetVariantField,
    /// `is_variant`: a checked, spec-only native enum test.
    IsVariant,
    /// `constrain_type`: erased from every position of an `ensures` list;
    /// elsewhere an ordinary Spec intrinsic with two Spec arguments.
    ConstrainType,
    /// `no_method_body`: the body of a trait method without a default.
    NoMethodBody,
    /// `dummy_capture_new`: part of the closure encoding.
    DummyCaptureNew,
    /// `dummy_capture_consume`: part of the closure encoding.
    DummyCaptureConsume,
    /// The mathematical integer type `int`.
    Int,
    /// The natural number type `nat`.
    Nat,
    /// The spec function type `FnSpec` (`spec_fn(..) -> ..`).
    FnSpec,
    /// The `Ghost<T>` wrapper type.
    Ghost,
    /// The `Tracked<T>` wrapper type.
    Tracked,
    /// `is_smaller_than(a, b)`: the height of `a` is below `b`'s.
    IsSmallerThan,
    /// `is_smaller_than_lexicographic((a, ..), (b, ..))`, which
    /// `decreases_to!` expands to.
    IsSmallerThanLexicographic,
    /// A part of a chained comparison.
    Chained(ChainOp),
    /// `assert_by(p, { proof })`: `assert(p) by { proof }`.
    AssertBy,
    /// The one-block isolated BV assertion marker.
    AssertBitvectorBy,
    /// `forall(|x| body)`.
    Forall,
    /// `exists(|x| body)`.
    Exists,
    /// `choose(|x| cond)`.
    Choose,
    /// `choose_tuple(|x, y| cond)`.
    ChooseTuple,
    /// `with_triggers(((t1, t2), (t3,)), body)`: `#![trigger ..]`.
    WithTriggers,
    /// `assert_forall_by(|x| { requires(r); ensures(e); proof })`:
    /// `assert forall|x| r implies e by { proof }`.
    AssertForallBy,
    /// `closure_to_fn_spec(closure)`: a closure in ghost code.
    ClosureToFnSpec,
    /// Any other `verus::` item. The reader refuses code that uses one.
    Other,
}

impl VerusItem {
    /// The item named by a diagnostic-item name, or `None` when the name is
    /// not a Verus item.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        if !name.starts_with(VERUS_PREFIX) {
            return None;
        }
        let Some(short) = name.strip_prefix(BUILTIN_PREFIX) else {
            return Some(Self::Other);
        };
        Some(builtin_item(short))
    }

    /// True for the markers that may only appear as leading header
    /// statements of a function body.
    #[must_use]
    pub const fn is_header(self) -> bool {
        matches!(
            self,
            Self::Requires
                | Self::Ensures
                | Self::Recommends
                | Self::OtherHeader
                | Self::OpensInvariantsNone
                | Self::NoUnwind
        )
    }
}

/// The item for a `verus_builtin` diagnostic-item name without its prefix.
fn builtin_item(short: &str) -> VerusItem {
    use VerusItem as V;
    match short {
        "arch_word_bits" => V::ArchWordBits,
        "global_size_of" => V::GlobalSizeOf,
        "requires" => V::Requires,
        "ensures" => V::Ensures,
        "recommends" => V::Recommends,
        "returns"
        | "invariant"
        | "invariant_except_break"
        | "decreases"
        | "decreases_when"
        | "decreases_by"
        | "recommends_by"
        | "opens_invariants"
        | "opens_invariants_any"
        | "opens_invariants_except"
        | "opens_invariants_set"
        | "no_unwind_when"
        | "extra_dependency"
        | "default_ensures" => V::OtherHeader,
        "opens_invariants_none" => V::OpensInvariantsNone,
        "no_unwind" => V::NoUnwind,
        "assert_" => V::Assert,
        "assume_" => V::Assume,
        "admit" => V::Admit,
        "reveal_hide" => V::RevealHide,
        "reveal_hide_internal_path" => V::RevealHideInternalPath,
        "imply" => V::Imply,
        "spec_eq" => V::SpecEq,
        "equal" => V::Equal,
        "SpecOrd::spec_lt" => V::SpecOrd(OrdOp::Lt),
        "SpecOrd::spec_le" => V::SpecOrd(OrdOp::Le),
        "SpecOrd::spec_gt" => V::SpecOrd(OrdOp::Gt),
        "SpecOrd::spec_ge" => V::SpecOrd(OrdOp::Ge),
        "SpecAdd::spec_add" => V::SpecArith(SpecArith::Add),
        "SpecSub::spec_sub" => V::SpecArith(SpecArith::Sub),
        "SpecMul::spec_mul" => V::SpecArith(SpecArith::Mul),
        "SpecEuclideanOrRealDiv::spec_euclidean_or_real_div" => V::SpecArith(SpecArith::Div),
        "SpecEuclideanMod::spec_euclidean_mod" => V::SpecArith(SpecArith::Mod),
        "SpecNeg::spec_neg" => V::SpecNeg,
        "SpecBitAnd::spec_bitand" => V::SpecBitwise(SpecBitwise::And),
        "SpecBitOr::spec_bitor" => V::SpecBitwise(SpecBitwise::Or),
        "SpecBitXor::spec_bitxor" => V::SpecBitwise(SpecBitwise::Xor),
        "SpecShl::spec_shl" => V::SpecBitwise(SpecBitwise::Shl),
        "SpecShr::spec_shr" => V::SpecBitwise(SpecBitwise::Shr),
        "add" => V::BuiltinArith(BuiltinArith::Add),
        "sub" => V::BuiltinArith(BuiltinArith::Sub),
        "mul" => V::BuiltinArith(BuiltinArith::Mul),
        "spec_literal_integer" => V::SpecLiteralInteger,
        "spec_literal_int" => V::SpecLiteralInt,
        "spec_literal_nat" => V::SpecLiteralNat,
        "spec_cast_integer" => V::SpecCastInteger,
        "old" => V::Old,
        "get_variant_field" => V::GetVariantField,
        "is_variant" => V::IsVariant,
        "constrain_type" => V::ConstrainType,
        "no_method_body" => V::NoMethodBody,
        "dummy_capture_new" => V::DummyCaptureNew,
        "dummy_capture_consume" => V::DummyCaptureConsume,
        "int" => V::Int,
        "nat" => V::Nat,
        "FnSpec" => V::FnSpec,
        "Ghost" => V::Ghost,
        "Tracked" => V::Tracked,
        "is_smaller_than" => V::IsSmallerThan,
        "is_smaller_than_lexicographic" => V::IsSmallerThanLexicographic,
        "spec_chained_value" => V::Chained(ChainOp::Value),
        "spec_chained_le" => V::Chained(ChainOp::Le),
        "spec_chained_lt" => V::Chained(ChainOp::Lt),
        "spec_chained_ge" => V::Chained(ChainOp::Ge),
        "spec_chained_gt" => V::Chained(ChainOp::Gt),
        "spec_chained_eq" => V::Chained(ChainOp::Eq),
        "spec_chained_cmp" => V::Chained(ChainOp::Cmp),
        "assert_by" => V::AssertBy,
        "assert_bitvector_by" => V::AssertBitvectorBy,
        "forall" => V::Forall,
        "exists" => V::Exists,
        "choose" => V::Choose,
        "choose_tuple" => V::ChooseTuple,
        "with_triggers" => V::WithTriggers,
        "assert_forall_by" => V::AssertForallBy,
        "closure_to_fn_spec" => V::ClosureToFnSpec,
        _ => V::Other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_map_to_items() {
        assert_eq!(
            VerusItem::from_name("verus::verus_builtin::requires"),
            Some(VerusItem::Requires)
        );
        assert_eq!(
            VerusItem::from_name("verus::verus_builtin::SpecOrd::spec_le"),
            Some(VerusItem::SpecOrd(OrdOp::Le))
        );
        assert_eq!(
            VerusItem::from_name("verus::verus_builtin::decreases"),
            Some(VerusItem::OtherHeader)
        );
    }

    #[test]
    fn unknown_verus_names_are_other_and_foreign_names_are_none() {
        assert_eq!(
            VerusItem::from_name("verus::verus_builtin::forall"),
            Some(VerusItem::Forall)
        );
        assert_eq!(
            VerusItem::from_name("verus::verus_builtin::assert_bit_vector"),
            Some(VerusItem::Other)
        );
        assert_eq!(
            VerusItem::from_name("verus::vstd::seq::Seq::len"),
            Some(VerusItem::Other)
        );
        assert_eq!(VerusItem::from_name("Option"), None);
        assert_eq!(VerusItem::from_name("verus_builtin::requires"), None);
    }

    #[test]
    fn header_markers() {
        assert!(VerusItem::Ensures.is_header());
        assert!(VerusItem::OtherHeader.is_header());
        assert!(!VerusItem::Assert.is_header());
    }
}
