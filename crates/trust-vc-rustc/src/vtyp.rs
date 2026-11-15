//! Types as Verus names them in diagnostics.
//!
//! Verus rejects a spec `==` or `!=` whose operand types are neither equal
//! nor both integers, and names both types in the message
//! (`rust_verify/src/fn_call_to_vir.rs`, the `SpecEq` arm;
//! `vir/src/ast_util.rs`, `typ_to_diagnostic_str`). The reader reproduces that
//! check, so it needs the same view of types: wrappers such as `&`, `Box`,
//! `Rc`, `Arc`, `Ghost` and `Tracked` are decorations that the comparison
//! looks through at the top level, and paths are printed with their crate
//! name (`core::option::Option<u64>`).
//!
//! The rustc layer builds a [`VTyp`] from a `rustc_middle` type; this module
//! only compares and prints.

use trust_vc_vcir::IntRange;

/// A wrapper type that spec equality looks through.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Decoration {
    /// `&T`.
    Ref,
    /// `&mut T`.
    MutRef,
    /// `Box<T>`.
    Box,
    /// `Rc<T>`.
    Rc,
    /// `Arc<T>`.
    Arc,
    /// `Ghost<T>`.
    Ghost,
    /// `Tracked<T>`.
    Tracked,
}

/// A type, in the shape Verus prints it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VTyp {
    /// `bool`.
    Bool,
    /// An integer type, including `int` and `nat`.
    Int(IntRange),
    /// A tuple; `()` is the empty tuple.
    Tuple(Vec<VTyp>),
    /// A struct, enum or union, by crate-qualified path.
    Datatype {
        /// `core::option::Option`, `test_crate::Foo`, ...
        path: String,
        /// Type arguments.
        args: Vec<VTyp>,
    },
    /// `spec_fn(args) -> ret`.
    SpecFn(Vec<VTyp>, Box<VTyp>),
    /// A type parameter, by name.
    Param(String),
    /// `<Self as Trait<args>>::Name`.
    Projection {
        /// The `Self` type.
        self_ty: Box<VTyp>,
        /// Crate-qualified path of the trait.
        trait_path: String,
        /// Trait arguments after `Self`.
        trait_args: Vec<VTyp>,
        /// Name of the associated type.
        name: String,
    },
    /// The type of one closure expression: its kind (`Fn`, `FnMut`,
    /// `FnOnce`), parameter types and return type. Two closure types are
    /// equal only when they come from the same closure expression, which
    /// `id` identifies within the crate.
    AnonymousClosure {
        /// `Fn`, `FnMut` or `FnOnce`.
        kind: &'static str,
        /// Parameter types.
        args: Vec<VTyp>,
        /// Return type.
        ret: Box<VTyp>,
        /// The closure's identity within the crate.
        id: u32,
    },
    /// A decorated type.
    Decorate(Decoration, Box<VTyp>),
    /// `!`.
    Never,
}

impl VTyp {
    /// The type with its outer decorations removed (Verus's
    /// `undecorate_typ`). Decorations nested inside other types stay.
    #[must_use]
    pub fn undecorate(&self) -> &Self {
        let mut ty = self;
        while let Self::Decorate(_, inner) = ty {
            ty = inner;
        }
        ty
    }

    /// Verus's diagnostic spelling of the type.
    #[must_use]
    pub fn to_diagnostic_string(&self) -> String {
        match self {
            Self::Bool => "bool".to_string(),
            Self::Int(range) => int_range_name(*range).to_string(),
            Self::Tuple(elems) => {
                // A one-element tuple keeps its trailing comma: `(T,)`.
                let comma = if elems.len() == 1 { "," } else { "" };
                format!("({}{comma})", comma_separated(elems))
            }
            Self::Datatype { path, args } => format!("{path}{}", angle_args(args)),
            Self::SpecFn(args, ret) => format!(
                "spec_fn({}) -> {}",
                comma_separated(args),
                ret.to_diagnostic_string()
            ),
            Self::Param(name) => name.clone(),
            Self::AnonymousClosure {
                kind, args, ret, ..
            } => format!(
                "AnonymousClosure({kind})({}) -> {}",
                comma_separated(args),
                ret.to_diagnostic_string()
            ),
            Self::Projection {
                self_ty,
                trait_path,
                trait_args,
                name,
            } => format!(
                "<{} as {trait_path}{}>::{name}",
                self_ty.to_diagnostic_string(),
                angle_args(trait_args)
            ),
            Self::Decorate(Decoration::Ref, inner) => format!("&{}", inner.to_diagnostic_string()),
            Self::Decorate(Decoration::MutRef, inner) => {
                format!("&mut {}", inner.to_diagnostic_string())
            }
            Self::Decorate(decoration, inner) => {
                format!("{decoration:?}<{}>", inner.to_diagnostic_string())
            }
            Self::Never => "!".to_string(),
        }
    }

    /// True for integer types once outer decorations are removed.
    #[must_use]
    pub fn is_integer(&self) -> bool {
        matches!(self.undecorate(), Self::Int(_))
    }
}

/// May `lhs == rhs` appear in spec code? Verus allows it when the undecorated
/// types are equal, or both are `bool`, or both are integers.
#[must_use]
pub fn spec_eq_compatible(lhs: &VTyp, rhs: &VTyp) -> bool {
    let (lhs, rhs) = (lhs.undecorate(), rhs.undecorate());
    lhs == rhs || (lhs.is_integer() && rhs.is_integer())
}

/// Verus's name for an integer type.
#[must_use]
pub const fn int_range_name(range: IntRange) -> &'static str {
    match range {
        IntRange::Int => "int",
        IntRange::Nat => "nat",
        IntRange::U(8) => "u8",
        IntRange::U(16) => "u16",
        IntRange::U(32) => "u32",
        IntRange::U(64) => "u64",
        IntRange::U(128) => "u128",
        IntRange::I(8) => "i8",
        IntRange::I(16) => "i16",
        IntRange::I(32) => "i32",
        IntRange::I(64) => "i64",
        IntRange::I(128) => "i128",
        IntRange::U(_) => "u?",
        IntRange::I(_) => "i?",
        IntRange::USize => "usize",
        IntRange::ISize => "isize",
        IntRange::Char => "char",
    }
}

fn comma_separated(tys: &[VTyp]) -> String {
    tys.iter()
        .map(VTyp::to_diagnostic_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn angle_args(tys: &[VTyp]) -> String {
    if tys.is_empty() {
        String::new()
    } else {
        format!("<{}>", comma_separated(tys))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn option(inner: VTyp) -> VTyp {
        VTyp::Datatype {
            path: "core::option::Option".to_string(),
            args: vec![inner],
        }
    }

    /// The five type pairs of upstream `basic.rs`'s `test_spec_eq_type_error_*`
    /// cases print as the reference Verus run printed them.
    #[test]
    fn prints_like_verus() {
        let u64_ = VTyp::Int(IntRange::U(64));
        assert_eq!(u64_.to_diagnostic_string(), "u64");
        assert_eq!(
            option(u64_.clone()).to_diagnostic_string(),
            "core::option::Option<u64>"
        );
        let arc = VTyp::Decorate(Decoration::Arc, Box::new(option(u64_.clone())));
        assert_eq!(
            arc.undecorate().to_diagnostic_string(),
            "core::option::Option<u64>"
        );
        let spec_fn = VTyp::SpecFn(vec![u64_.clone()], Box::new(VTyp::Int(IntRange::Nat)));
        assert_eq!(spec_fn.to_diagnostic_string(), "spec_fn(u64) -> nat");
        let pair = VTyp::Tuple(vec![u64_.clone(), VTyp::Int(IntRange::Nat)]);
        assert_eq!(pair.to_diagnostic_string(), "(u64, nat)");
        let projection = VTyp::Projection {
            self_ty: Box::new(VTyp::Param("X".to_string())),
            trait_path: "test_crate::A".to_string(),
            trait_args: vec![],
            name: "AT".to_string(),
        };
        assert_eq!(
            projection.to_diagnostic_string(),
            "<X as test_crate::A>::AT"
        );
        assert_eq!(
            VTyp::Tuple(vec![VTyp::Bool]).to_diagnostic_string(),
            "(bool,)"
        );
        let closure = VTyp::AnonymousClosure {
            kind: "Fn",
            args: vec![VTyp::Int(IntRange::I(32))],
            ret: Box::new(VTyp::Int(IntRange::I(32))),
            id: 7,
        };
        assert_eq!(
            closure.to_diagnostic_string(),
            "AnonymousClosure(Fn)(i32) -> i32"
        );
        assert_eq!(VTyp::Tuple(vec![]).to_diagnostic_string(), "()");
    }

    #[test]
    fn compatibility() {
        let u64_ = VTyp::Int(IntRange::U(64));
        let nat = VTyp::Int(IntRange::Nat);
        assert!(spec_eq_compatible(&u64_, &nat));
        assert!(spec_eq_compatible(&VTyp::Bool, &VTyp::Bool));
        assert!(!spec_eq_compatible(&u64_, &option(u64_.clone())));
        // Outer decorations are transparent...
        let boxed = VTyp::Decorate(Decoration::Box, Box::new(option(u64_.clone())));
        assert!(spec_eq_compatible(&boxed, &option(u64_.clone())));
        // ...nested ones are not.
        let nested = option(VTyp::Decorate(Decoration::Box, Box::new(u64_.clone())));
        assert!(!spec_eq_compatible(&nested, &option(u64_)));
        assert!(!spec_eq_compatible(&VTyp::Bool, &nat));
        // Closure types are equal only to themselves.
        let closure = |id| VTyp::AnonymousClosure {
            kind: "Fn",
            args: vec![],
            ret: Box::new(VTyp::Bool),
            id,
        };
        assert!(spec_eq_compatible(&closure(1), &closure(1)));
        assert!(!spec_eq_compatible(&closure(1), &closure(2)));
        assert!(!spec_eq_compatible(&closure(1), &nat));
    }
}
