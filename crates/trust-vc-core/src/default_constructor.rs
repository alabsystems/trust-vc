// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Type-directed model of the `Default::default()` constructor family.
//!
//! The value of `Default::default()` is fixed by its EXPECTED type, which the
//! source spells in one of three ways (upstream `default_trait.rs`):
//!
//! * `<Ty>::default()` / `<Ty as core::default::Default>::default()` — the
//!   type is the qualified path's `qself`;
//! * `let b: Ty = Default::default()` / `fn f() -> Ty { Default::default() }`
//!   — the type is the binding's declaration or the function's return type;
//! * `Ty::default()` / `Ty::<A>::default()` — the type is the receiver path.
//!
//! This module holds the ONE model shared by the extraction (which resolves
//! the first two spellings, where only it knows the expected type) and the
//! lowering (which resolves the receiver spelling): the default of a type
//! rendered as a SOURCE expression the lowering already models.
//!
//! Every rule is Rust's own `impl Default` for the type, read from `core` /
//! `alloc`: integers are `0`, `bool` is `false`, `char` is `'\0'`, floats are
//! `0.0`, `&str` and `String` are the empty string, `Option<T>` is `None`, the
//! `PhantomData<T>` marker is its unit value, a tuple is the tuple of its
//! elements' defaults, `Vec`/`VecDeque`/`HashMap`/`HashSet` are empty, and the
//! smart pointers `Box<T>`/`Rc<T>`/`Arc<T>` hold `T`'s default (their payload
//! IS the modelled value — `Box::new(x)` lowers to `x`). A user type or a type
//! parameter renders as its own `Ty::default()` receiver spelling, which the
//! lowering resolves ONLY through a registered symbol (a hand-written `impl
//! Default` body axiom, a `#[derive(Default)]` synthesized body, or the
//! per-type-parameter constant); anything else keeps failing closed with the
//! pre-existing "unknown return type" refusal.

use quote::ToTokens;

/// The default of `ty` as a source expression, or `None` when the type's
/// `Default` is not modelled (the caller then fails closed).
pub(crate) fn default_value_source_for_type(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Paren(paren) => default_value_source_for_type(&paren.elem),
        syn::Type::Group(group) => default_value_source_for_type(&group.elem),
        syn::Type::Tuple(tuple) => {
            if tuple.elems.is_empty() {
                return Some("()".to_string());
            }
            let elems = tuple
                .elems
                .iter()
                .map(default_value_source_for_type)
                .collect::<Option<Vec<_>>>()?;
            let trailing = if elems.len() == 1 { "," } else { "" };
            Some(format!("({}{trailing})", elems.join(", ")))
        }
        // `impl Default for &str` is the empty string. No other reference type
        // has a `Default` impl that this model spells (`&[T]` / `&mut T` stay
        // fail-closed).
        syn::Type::Reference(reference) => {
            if reference.mutability.is_some() {
                return None;
            }
            match reference.elem.as_ref() {
                syn::Type::Path(elem) if path_is_bare_ident(&elem.path, "str") => {
                    Some("\"\"".to_string())
                }
                _ => None,
            }
        }
        syn::Type::Path(type_path) => {
            if type_path.qself.is_some() {
                return None;
            }
            default_value_source_for_path(&type_path.path)
        }
        _ => None,
    }
}

fn path_is_bare_ident(path: &syn::Path, ident: &str) -> bool {
    path.segments.len() == 1
        && path.segments[0].ident == ident
        && matches!(path.segments[0].arguments, syn::PathArguments::None)
}

fn default_value_source_for_path(path: &syn::Path) -> Option<String> {
    let last = path.segments.last()?;
    let name = last.ident.to_string();
    let type_args: Vec<&syn::Type> = match &last.arguments {
        syn::PathArguments::None => Vec::new(),
        syn::PathArguments::AngleBracketed(args) => {
            let mut types = Vec::new();
            for arg in &args.args {
                match arg {
                    syn::GenericArgument::Type(ty) => types.push(ty),
                    // A lifetime argument is not a type; anything else (a const
                    // generic, an associated-type binding) is out of scope.
                    syn::GenericArgument::Lifetime(_) => {}
                    _ => return None,
                }
            }
            types
        }
        syn::PathArguments::Parenthesized(_) => return None,
    };
    // Every leading segment must be a plain module segment.
    let prefix: Vec<String> = path
        .segments
        .iter()
        .take(path.segments.len() - 1)
        .map(|segment| {
            matches!(segment.arguments, syn::PathArguments::None).then(|| segment.ident.to_string())
        })
        .collect::<Option<_>>()?;
    let prefix: Vec<&str> = prefix.iter().map(String::as_str).collect();

    if type_args.is_empty() {
        if let Some(primitive) = primitive_default_source(&name) {
            // A primitive is only itself when spelled bare (`u32`), or through
            // its `core::primitive` home; a user module could not shadow it.
            return matches!(
                prefix.as_slice(),
                [] | ["core", "primitive"] | ["std", "primitive"]
            )
            .then_some(primitive);
        }
        // `String::new()` is the tracked-length empty constructor (the
        // collection-constructor lane registers its length as the literal 0),
        // which is what `s.view().len()` reads; a bare `""` literal carries no
        // tracked length in the default (non-native-strings) lane.
        if name == "String"
            && matches!(
                prefix.as_slice(),
                [] | ["std", "string"] | ["alloc", "string"]
            )
        {
            return Some("String::new()".to_string());
        }
        // A user type or a type parameter: its own receiver spelling, resolved
        // by the lowering only through a registered `Ty::default` symbol.
        return prefix.is_empty().then(|| format!("{name}::default()"));
    }

    let args = type_args
        .iter()
        .map(|ty| ty.to_token_stream().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    match (name.as_str(), type_args.as_slice()) {
        ("Option", [_])
            if matches!(
                prefix.as_slice(),
                [] | ["core", "option"] | ["std", "option"]
            ) =>
        {
            Some(format!("Option::<{args}>::None"))
        }
        ("Vec", [_]) if matches!(prefix.as_slice(), [] | ["std", "vec"] | ["alloc", "vec"]) => {
            Some(format!("Vec::<{args}>::new()"))
        }
        ("VecDeque", [_]) if std_collections_prefix(&prefix) => {
            Some(format!("VecDeque::<{args}>::new()"))
        }
        ("HashSet", [_]) if std_collections_prefix(&prefix) => {
            Some(format!("HashSet::<{args}>::new()"))
        }
        ("HashMap", [_, _]) if std_collections_prefix(&prefix) => {
            Some(format!("HashMap::<{args}>::new()"))
        }
        // Transparent ownership wrappers: the payload is the modelled value.
        ("Box", [inner])
            if matches!(
                prefix.as_slice(),
                [] | ["std", "boxed"] | ["alloc", "boxed"]
            ) =>
        {
            default_value_source_for_type(inner)
        }
        ("Rc", [inner]) if matches!(prefix.as_slice(), [] | ["std", "rc"] | ["alloc", "rc"]) => {
            default_value_source_for_type(inner)
        }
        ("Arc", [inner])
            if matches!(prefix.as_slice(), [] | ["std", "sync"] | ["alloc", "sync"]) =>
        {
            default_value_source_for_type(inner)
        }
        ("PhantomData", [_])
            if matches!(
                prefix.as_slice(),
                [] | ["core", "marker"] | ["std", "marker"]
            ) =>
        {
            // Keep the spelling the source used: the lowering's PhantomData
            // constructor accepts the bare name and the `core`/`std::marker`
            // homes, and a bare name is shadowable by a same-named local.
            let home = if prefix.is_empty() {
                String::new()
            } else {
                format!("{}::", prefix.join("::"))
            };
            Some(format!("{home}PhantomData::<{args}>"))
        }
        // A generic user type: its own receiver spelling with the type
        // arguments as a turbofish.
        _ if prefix.is_empty() => Some(format!("{name}::<{args}>::default()")),
        _ => None,
    }
}

fn std_collections_prefix(prefix: &[&str]) -> bool {
    matches!(
        prefix,
        [] | ["std", "collections"] | ["alloc", "collections"]
    )
}

fn primitive_default_source(name: &str) -> Option<String> {
    match name {
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "usize" => Some(format!("0{name}")),
        "bool" => Some("false".to_string()),
        "char" => Some("'\\0'".to_string()),
        "f32" | "f64" => Some(format!("0.0{name}")),
        // The extraction renders `<&'static str>::default()` with the
        // reference stripped (`extract_type_string`), so the bare `str` arrives
        // here; `str` itself has no `Default`, so the only way to reach it is
        // through `&str`, whose default is the empty string.
        "str" => Some("\"\"".to_string()),
        _ => None,
    }
}

/// True when `source` (as produced by [`default_value_source_for_type`]) is a
/// receiver spelling `Ty::default()` / `Ty::<A>::default()` — i.e. names a user
/// type or a type parameter rather than a modelled literal/constructor.
pub(crate) fn source_is_receiver_default_call(source: &str) -> bool {
    source.ends_with("::default()")
}

/// True for the bare trait spelling `Default::default()` (also through its
/// `core::default` / `std::default` home), whose value is fixed only by the
/// context's expected type.
pub(crate) fn is_bare_default_trait_call(expr: &syn::Expr) -> bool {
    let syn::Expr::Call(call) = expr else {
        return false;
    };
    if !call.args.is_empty() {
        return false;
    }
    let syn::Expr::Path(path) = call.func.as_ref() else {
        return false;
    };
    if path.qself.is_some() {
        return false;
    }
    let idents: Vec<String> = path
        .path
        .segments
        .iter()
        .map(|segment| {
            matches!(segment.arguments, syn::PathArguments::None).then(|| segment.ident.to_string())
        })
        .collect::<Option<_>>()
        .unwrap_or_default();
    let idents: Vec<&str> = idents.iter().map(String::as_str).collect();
    matches!(
        idents.as_slice(),
        ["Default", "default"]
            | ["core", "default", "Default", "default"]
            | ["std", "default", "Default", "default"]
    )
}

/// True when the qualified path of a no-arg `default` call names the
/// `Default` trait (or no trait at all): `<Ty>::default()` and
/// `<Ty as core::default::Default>::default()`. A qself call through some
/// OTHER trait's `default` method is not this constructor.
pub(crate) fn qself_call_is_default_constructor(path: &syn::ExprPath) -> bool {
    let Some(qself) = path.qself.as_ref() else {
        return false;
    };
    let segments = &path.path.segments;
    let Some(last) = segments.last() else {
        return false;
    };
    if last.ident != "default" || !matches!(last.arguments, syn::PathArguments::None) {
        return false;
    }
    if qself.position == 0 {
        return segments.len() == 1;
    }
    // The trait path is `segments[..position]`; its last segment must be the
    // `Default` trait and `default` must be the method right after it.
    qself.position + 1 == segments.len()
        && segments
            .iter()
            .nth(qself.position - 1)
            .is_some_and(|trait_seg| trait_seg.ident == "Default")
}

/// For a receiver-spelled no-arg call `Recv::default()` / `Recv::<A>::default()`
/// / `a::b::Recv::default()` (no qself), the receiver rendered as a type
/// (`Recv`, `Recv<A>`, `a::b::Recv`). `None` for any other expression,
/// including the bare trait spelling.
pub(crate) fn receiver_default_call_type(expr: &syn::Expr) -> Option<syn::Type> {
    let syn::Expr::Call(call) = expr else {
        return None;
    };
    if !call.args.is_empty() {
        return None;
    }
    let syn::Expr::Path(path) = call.func.as_ref() else {
        return None;
    };
    if path.qself.is_some() || is_bare_default_trait_call(expr) {
        return None;
    }
    default_receiver_syn_type(&path.path)
}

/// The receiver of a `…::default` path as a type: every segment but the last,
/// with a turbofish (`Vec::<u32>`) read as ordinary type arguments (`Vec<u32>`).
pub(crate) fn default_receiver_syn_type(path: &syn::Path) -> Option<syn::Type> {
    let last = path.segments.last()?;
    if last.ident != "default"
        || !matches!(last.arguments, syn::PathArguments::None)
        || path.segments.len() < 2
    {
        return None;
    }
    let mut receiver = syn::Path {
        leading_colon: path.leading_colon,
        segments: path
            .segments
            .iter()
            .take(path.segments.len() - 1)
            .cloned()
            .collect(),
    };
    for segment in &mut receiver.segments {
        if let syn::PathArguments::AngleBracketed(args) = &mut segment.arguments {
            args.colon2_token = None;
        }
    }
    Some(syn::Type::Path(syn::TypePath {
        qself: None,
        path: receiver,
    }))
}

/// True when `ty` is one of the transparent ownership wrappers whose payload
/// is the modelled value, so a `*p` read of a binding of this type is the
/// binding's value itself.
pub(crate) fn is_smart_pointer_type(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Paren(paren) => is_smart_pointer_type(&paren.elem),
        syn::Type::Group(group) => is_smart_pointer_type(&group.elem),
        syn::Type::Path(type_path) if type_path.qself.is_none() => {
            let Some(last) = type_path.path.segments.last() else {
                return false;
            };
            matches!(last.ident.to_string().as_str(), "Box" | "Rc" | "Arc")
                && matches!(last.arguments, syn::PathArguments::AngleBracketed(_))
        }
        _ => false,
    }
}

/// True for a smart-pointer constructor call `Box::new(x)` / `Rc::new(x)` /
/// `Arc::new(x)` (any module prefix), whose value the lowering models as `x`.
pub(crate) fn is_smart_pointer_new_call(expr: &syn::Expr) -> bool {
    let syn::Expr::Call(call) = expr else {
        return false;
    };
    if call.args.len() != 1 {
        return false;
    }
    let syn::Expr::Path(path) = call.func.as_ref() else {
        return false;
    };
    if path.qself.is_some() || path.path.segments.len() < 2 {
        return false;
    }
    let segments = &path.path.segments;
    segments[segments.len() - 1].ident == "new"
        && matches!(
            segments[segments.len() - 2].ident.to_string().as_str(),
            "Box" | "Rc" | "Arc"
        )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(ty: &str) -> Option<String> {
        default_value_source_for_type(&syn::parse_str::<syn::Type>(ty).expect("type parses"))
    }

    #[test]
    fn primitives_and_strings() {
        assert_eq!(source("u32").as_deref(), Some("0u32"));
        assert_eq!(source("isize").as_deref(), Some("0isize"));
        assert_eq!(source("bool").as_deref(), Some("false"));
        assert_eq!(source("char").as_deref(), Some("'\\0'"));
        assert_eq!(source("f32").as_deref(), Some("0.0f32"));
        assert_eq!(source("f64").as_deref(), Some("0.0f64"));
        assert_eq!(source("&'static str").as_deref(), Some("\"\""));
        assert_eq!(source("&str").as_deref(), Some("\"\""));
        assert_eq!(source("String").as_deref(), Some("String::new()"));
        assert_eq!(source("&mut str"), None);
        assert_eq!(source("&[u8]"), None);
    }

    #[test]
    fn compound_shapes() {
        assert_eq!(source("()").as_deref(), Some("()"));
        assert_eq!(source("(u32,)").as_deref(), Some("(0u32,)"));
        assert_eq!(
            source("(u32, bool, char)").as_deref(),
            Some("(0u32, false, '\\0')")
        );
        assert_eq!(
            source("Option<u32>").as_deref(),
            Some("Option::<u32>::None")
        );
        assert_eq!(source("Vec<u32>").as_deref(), Some("Vec::<u32>::new()"));
        assert_eq!(
            source("std::collections::VecDeque<u32>").as_deref(),
            Some("VecDeque::<u32>::new()")
        );
        assert_eq!(
            source("HashMap<u32, u32>").as_deref(),
            Some("HashMap::<u32, u32>::new()")
        );
        assert_eq!(
            source("HashSet<u32>").as_deref(),
            Some("HashSet::<u32>::new()")
        );
        assert_eq!(source("Box<u32>").as_deref(), Some("0u32"));
        assert_eq!(source("Rc<Vec<u32>>").as_deref(), Some("Vec::<u32>::new()"));
        assert_eq!(source("Arc<(u32, bool)>").as_deref(), Some("(0u32, false)"));
        assert_eq!(
            source("core::marker::PhantomData<u32>").as_deref(),
            Some("core::marker::PhantomData::<u32>")
        );
        assert_eq!(
            source("PhantomData<u32>").as_deref(),
            Some("PhantomData::<u32>")
        );
        // An unmodelled std generic renders as a receiver spelling, which the
        // lowering resolves only through a registered `BTreeMap::default`
        // symbol — there is none, so it keeps the fail-closed refusal.
        assert_eq!(
            source("BTreeMap<u32, u32>").as_deref(),
            Some("BTreeMap::<u32, u32>::default()")
        );
        assert!(source_is_receiver_default_call(
            &source("BTreeMap<u32, u32>").unwrap()
        ));
    }

    #[test]
    fn user_types_render_as_their_receiver_spelling() {
        assert_eq!(source("MyType").as_deref(), Some("MyType::default()"));
        assert_eq!(source("T").as_deref(), Some("T::default()"));
        assert_eq!(
            source("Wrapper<u32>").as_deref(),
            Some("Wrapper::<u32>::default()")
        );
        assert_eq!(source("Box<MyType>").as_deref(), Some("MyType::default()"));
        assert!(source_is_receiver_default_call("MyType::default()"));
        assert!(!source_is_receiver_default_call("0u32"));
        assert_eq!(source("m::Hidden"), None);
    }

    #[test]
    fn spellings_are_classified() {
        let parse = |s: &str| syn::parse_str::<syn::Expr>(s).expect("expr parses");
        assert!(is_bare_default_trait_call(&parse("Default::default()")));
        assert!(is_bare_default_trait_call(&parse(
            "core::default::Default::default()"
        )));
        assert!(!is_bare_default_trait_call(&parse("u32::default()")));
        assert!(!is_bare_default_trait_call(&parse("Default::default(1)")));
        let recv = receiver_default_call_type(&parse("Vec::<u32>::default()")).expect("receiver");
        assert_eq!(
            recv.to_token_stream().to_string().replace(' ', ""),
            "Vec<u32>"
        );
        assert!(receiver_default_call_type(&parse("Default::default()")).is_none());
        let qself = |s: &str| match parse(s) {
            syn::Expr::Call(call) => match *call.func {
                syn::Expr::Path(path) => qself_call_is_default_constructor(&path),
                _ => false,
            },
            _ => false,
        };
        assert!(qself("<u32>::default()"));
        assert!(qself("<u32 as core::default::Default>::default()"));
        assert!(qself("<u32 as Default>::default()"));
        assert!(!qself("<u32 as Other>::default()"));
        assert!(!qself("u32::default()"));
        assert!(is_smart_pointer_type(&syn::parse_str("Box<u32>").unwrap()));
        assert!(is_smart_pointer_type(
            &syn::parse_str("std::sync::Arc<S>").unwrap()
        ));
        assert!(!is_smart_pointer_type(&syn::parse_str("Vec<u32>").unwrap()));
        assert!(is_smart_pointer_new_call(&parse("Box::new(1u32)")));
        assert!(!is_smart_pointer_new_call(&parse("Box::default()")));
    }
}
