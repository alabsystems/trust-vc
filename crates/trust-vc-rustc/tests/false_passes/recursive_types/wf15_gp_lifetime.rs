::verus_builtin_macros::verus!{
pub struct S<#[verifier::accept_recursive_types] 'a> { pub a: &'a u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
