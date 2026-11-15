::verus_builtin_macros::verus!{
pub struct S<#[verifier::accept_recursive_types] A> { pub a: A }
pub struct R { pub s: S<u8> }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
