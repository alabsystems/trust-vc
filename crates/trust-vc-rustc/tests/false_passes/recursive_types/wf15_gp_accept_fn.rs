::verus_builtin_macros::verus!{
fn g<#[verifier::accept_recursive_types] A>(a: u8) -> u8 { a }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
