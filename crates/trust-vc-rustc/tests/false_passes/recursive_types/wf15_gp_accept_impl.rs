::verus_builtin_macros::verus!{
pub struct S<A> { pub a: A }
impl<#[verifier::accept_recursive_types] A> S<A> { fn k() -> u8 { 1 } }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
