//! Unit tests of `untyped_binding_type.rs`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn infer(src: &str, peers: &[(&str, TrustVcType)]) -> Option<TrustVcType> {
    let block: syn::Block = syn::parse_str(src).expect("block");
    let (first, rest) = block.stmts.split_first().expect("a let");
    let Stmt::Local(local) = first else {
        panic!("first statement is a let");
    };
    let syn::Pat::Ident(ident) = &local.pat else {
        panic!("a plain binding");
    };
    let peers = peers.to_vec();
    let peer_type = move |name: &str| {
        peers
            .iter()
            .find(|(peer, _)| *peer == name)
            .map(|(_, ty)| ty.clone())
    };
    // `p8` is a file function whose `u8` parameter this lane reads; every
    // other callee (`g8`) is one it does not.
    let call_param = |call: &syn::ExprCall, index: usize| match &*call.func {
        syn::Expr::Path(path) if path.path.is_ident("p8") && index == 0 => Some(U8),
        _ => None,
    };
    let types = UseTypes {
        peer: &peer_type,
        call_param: &call_param,
    };
    infer_untyped_binding_type(&ident.ident.to_string(), rest, &types)
}

const U8: TrustVcType = TrustVcType::Uint { width: 8 };
const USIZE: TrustVcType = TrustVcType::Uint { width: 64 };
const I32: TrustVcType = TrustVcType::Int { width: 32 };

#[test]
fn a_typed_peer_fixes_the_type() {
    let src = "{ let mut w = 0; while i < 1 { w = 200; } let z = w + y; }";
    assert_eq!(infer(src, &[("y", U8)]), Some(U8));
    let src = "{ let mut i = 0; while i < n { invariant!(0 <= i); i = i + 1; } }";
    assert_eq!(infer(src, &[("n", USIZE)]), Some(USIZE));
    let src = "{ let mut w = 0; w = w + 1; let z: u8 = w; }";
    assert_eq!(infer(src, &[]), Some(U8));
    let src = "{ let mut w = 0; w += 7u8; }";
    assert_eq!(infer(src, &[]), Some(U8));
}

#[test]
fn a_peer_reached_through_an_operation_of_the_binding_types_it() {
    let src = "{ let mut w = 0; w = w + 100; let z = w - 1 + y; }";
    assert_eq!(infer(src, &[("y", U8)]), Some(U8));
    let src = "{ let mut w = 0; w = 250; let z = (w >> 1) + y; }";
    assert_eq!(infer(src, &[("y", U8)]), Some(U8));
    let src = "{ let mut w = 0; w = 250; if (w >> 1) < y { } }";
    assert_eq!(infer(src, &[("y", U8)]), Some(U8));
    let src = "{ let mut w = 0; w = 250; let z: u8 = w - 1; }";
    assert_eq!(infer(src, &[]), Some(U8));
}

#[test]
fn only_untyped_literal_peers_default_to_i32() {
    let src = "{ let mut i = 0; while i < 10 { invariant!(i <= 10); i = i + 1; } }";
    assert_eq!(infer(src, &[]), Some(I32));
    // A compound assignment is a statement of type `()`, not an operation of
    // the binding's type.
    let src = "{ let mut i = 0; while i < 10 { invariant!(i <= 10); i += 1; } }";
    assert_eq!(infer(src, &[]), Some(I32));
    let src = "{ let mut i = 1; while i < 64 { i <<= 1; i -= 0; } }";
    assert_eq!(infer(src, &[]), Some(I32));
    let src = "{ let mut i = 0; let s = k << i; let t = i as u64; let m = i.max(1) < 9; }";
    assert_eq!(infer(src, &[]), Some(I32));
    let src =
        "{ let mut i = 0; let t = (i - 1) as u64; let m = (i + 1).max(1) == 2; f(k << (i - 1)); }";
    assert_eq!(infer(src, &[]), Some(I32));
}

#[test]
fn an_unascribed_copy_is_read_through_its_own_uses() {
    // `let z = <w or an operation of its type>;`: `z` has `w`'s type.
    let src = "{ let mut w = 0; let z = w << 1; let q = z + y; }";
    assert_eq!(infer(src, &[("y", U8)]), Some(U8));
    let src = "{ let mut w = 0; let z = w; let q: u8 = z; }";
    assert_eq!(infer(src, &[]), Some(U8));
    // An unused copy fixes nothing; one whose use is not read decides nothing.
    let src = "{ let x = 5; let mut i = 0; while i < 2 { let _m = x.max(1); i = i + 1; } }";
    assert_eq!(infer(src, &[]), Some(I32));
    assert_eq!(
        infer("{ let mut w = 0; let z = w - 45; g8(z); }", &[]),
        None
    );
    // A copy that a later `let` shadows is followed only up to that `let`:
    // the `z` of `z + y` is the new binding, so nothing types `w`.
    let src = "{ let mut w = 0; let z = w; let z: u16 = 1; let q = z + y; }";
    assert_eq!(infer(src, &[("y", U8)]), Some(I32));
}

#[test]
fn a_trait_method_types_the_binding_through_its_signature() {
    // `Ord::{max, min, clamp}` arguments and `PartialEq`/`PartialOrd`/`Ord`
    // comparison arguments have the receiver's type, either way round.
    for src in [
        "{ let mut w = 0; let z = w.min(y); }",
        "{ let mut w = 0; let z = w.clamp(0, y); }",
        "{ let mut w = 0; let b = w.eq(&y); }",
        "{ let mut w = 0; if w.ne(&y) { } }",
        "{ let mut w = 0; let o = w.cmp(&y); }",
        "{ let mut w = 0; let z = y.min(w); }",
        "{ let mut w = 0; let b = y.lt(&w); }",
        // A `Self`-typed result is typed by its position.
        "{ let mut w = 0; let z = w.max(1) + y; }",
        "{ let mut w = 0; let b = w.clone() < y; }",
        "{ let mut w = 0; let z: u8 = w.max(1); }",
        "{ let mut w = 0; z = w.min(5); }",
    ] {
        assert_eq!(infer(src, &[("y", U8), ("z", U8)]), Some(U8), "{src}");
    }
    // A `Self`-typed result where nothing here types it, and a method this
    // reading does not know, decide nothing.
    for src in [
        "{ let mut w = 0; let z = w.max(1); g8(z); }",
        "{ let mut w = 0; g8(w.clone()); }",
        "{ let mut w = 0; let s = S { g: w.max(0) }; }",
        "{ let mut w = 0; let z = w.pow(2); }",
        "{ let mut w = 0; let z = w.wrapping_add(y); }",
    ] {
        assert_eq!(infer(src, &[("y", U8)]), None, "{src}");
    }
}

#[test]
fn an_unread_use_a_rebinding_or_a_typed_macro_peer_decides_nothing() {
    // A call argument: the parameter's type is not read here.
    assert_eq!(infer("{ let mut w = 0; f(w); }", &[]), None);
    // The name is rebound after the `let` by another pattern; a `let` that
    // shadows it ends its uses (`w + 1u8` reads the new `w`).
    assert_eq!(
        infer("{ let mut w = 0; let f = |w: u8| w + 1u8; w + 1u8; }", &[]),
        None
    );
    assert_eq!(
        infer("{ let mut w = 0; let w: u8 = 1; w + 1u8; }", &[]),
        Some(I32)
    );
    // A peer's name is rebound after the `let`.
    let src = "{ let mut w = 0; let y: u16 = 1; let z = w + y; }";
    assert_eq!(infer(src, &[("y", U8)]), None);
    // A typed peer only inside a macro.
    let src = "{ let mut w = 0; while w < 10 { invariant!(w <= y); w = w + 1; } }";
    assert_eq!(infer(src, &[("y", U8)]), None);
    // A peer of unknown type.
    assert_eq!(infer("{ let mut w = 0; let z = w + q; }", &[]), None);
    // An operation of the binding's type where this reading does not type
    // it: a call or method argument, a struct field, a tail, an index, a
    // conditional value.
    for src in [
        "{ let mut w = 0; g8(w - 45); }",
        "{ let mut w = 0; let s = S { g: w - 45 }; }",
        "{ let mut w = 0; v.push(w - 45); }",
        "{ let mut w = 0; w - 45 }",
        "{ let mut w = 0; let k = v[w - 1]; }",
        "{ let mut w = 0; let z = (if c { w - 1 } else { 0 }) + y; }",
        "{ let mut w = 0; g8(-w); }",
    ] {
        assert_eq!(infer(src, &[("y", U8)]), None, "{src}");
    }
    // Next to a typed place or peer it is typed there.
    let src = "{ let mut w = 0; let mut z: u8 = 0; z = w - 45; }";
    assert_eq!(
        infer(src, &[("z", U8)]),
        None,
        "`z` is rebound after the `let`"
    );
    let src = "{ let mut w = 0; z = w - 45; }";
    assert_eq!(infer(src, &[("z", U8)]), Some(U8));
    let src = "{ let mut w = 0; z += w - 45; }";
    assert_eq!(infer(src, &[("z", U8)]), Some(U8));
}

#[test]
fn a_call_argument_at_a_read_parameter_types_the_binding() {
    // `let a = 200 + 100; p8(a);` compiles under `#[allow(arithmetic_overflow)]`
    // and computes in `u8`.
    assert_eq!(infer("{ let a = 200 + 100; p8(a); }", &[]), Some(U8));
    assert_eq!(infer("{ let mut w = 0; p8(w - 45); }", &[]), Some(U8));
    assert_eq!(infer("{ let mut w = 0; let z = w; p8(z); }", &[]), Some(U8));
    // A callee the statements after the `let` re-bind is not the file
    // function, and an unread one decides nothing.
    assert_eq!(
        infer("{ let a = 1; let p8 = |x: u16| x; p8(a); }", &[]),
        None
    );
    assert_eq!(infer("{ let a = 1; g8(a); }", &[]), None);
}

#[test]
fn a_let_shadows_the_binding_for_the_rest_of_its_block() {
    let src = "{ let x = 7; let y = { let x = 5u16; x + 1u16 }; let z = x + 2u8; }";
    assert_eq!(infer(src, &[]), Some(U8));
    // The shadowing `let`'s initializer is still a use.
    assert_eq!(infer("{ let x = 7; let x = x + 1u8; }", &[]), Some(U8));
    assert_eq!(
        infer("{ let x = 7; let x = 5u16; let z = x + 1u16; }", &[]),
        Some(I32)
    );
    // Another pattern binding the name may stand anywhere.
    let src = "{ let x = 7; let f = |x: u16| x + 1u16; let z = x + 2u8; }";
    assert_eq!(infer(src, &[]), None);
}

#[test]
fn a_reference_to_the_binding_is_read_through_its_derefs() {
    assert_eq!(
        infer("{ let a = 200; let r = &a; p8(*r + 100); }", &[]),
        Some(U8)
    );
    assert_eq!(
        infer("{ let a = 200; let r = &a; let b = *r + 100 == 300; }", &[]),
        Some(I32)
    );
    assert_eq!(
        infer("{ let mut a = 0; let r = &mut a; *r = y; }", &[("y", U8)]),
        Some(U8)
    );
    // The reference itself passed on, or a method on it, decides nothing.
    assert_eq!(infer("{ let a = 200; let r = &a; f(r); }", &[]), None);
    assert_eq!(
        infer("{ let a = 200; let r = &a; let m = r.max(&1); }", &[]),
        None
    );
}

fn infer_elements(src: &str, peers: &[(&str, TrustVcType)]) -> Option<TrustVcType> {
    let block: syn::Block = syn::parse_str(src).expect("block");
    let (first, rest) = block.stmts.split_first().expect("a let");
    let Stmt::Local(local) = first else {
        panic!("first statement is a let");
    };
    let syn::Pat::Ident(ident) = &local.pat else {
        panic!("a plain binding");
    };
    let peers = peers.to_vec();
    let peer_type = move |name: &str| {
        peers
            .iter()
            .find(|(peer, _)| *peer == name)
            .map(|(_, ty)| ty.clone())
    };
    let call_param = |call: &syn::ExprCall, index: usize| match &*call.func {
        syn::Expr::Path(path) if path.path.is_ident("p8") && index == 0 => Some(U8),
        _ => None,
    };
    let types = UseTypes {
        peer: &peer_type,
        call_param: &call_param,
    };
    infer_untyped_element_type(&ident.ident.to_string(), rest, &types)
}

#[test]
fn an_array_of_untyped_literals_is_typed_by_the_uses_of_its_elements() {
    assert_eq!(
        infer_elements("{ let a = [200, 1]; p8(a[0]); }", &[]),
        Some(U8)
    );
    assert_eq!(
        infer_elements("{ let a = [200, 1]; let z = a[i] + y; }", &[("y", U8)]),
        Some(U8)
    );
    assert_eq!(
        infer_elements("{ let a = [200, 1]; let r = &a; p8(r[0] + 1); }", &[]),
        Some(U8)
    );
    assert_eq!(
        infer_elements(
            "{ let a = [1, 2]; let n = a.len(); let z = a[0] + 1 == 2; }",
            &[]
        ),
        Some(I32)
    );
    // The array itself passed on decides nothing.
    assert_eq!(
        infer_elements("{ let a = [200, 1]; f(a); let z = a[0] + 1; }", &[]),
        None
    );
}
