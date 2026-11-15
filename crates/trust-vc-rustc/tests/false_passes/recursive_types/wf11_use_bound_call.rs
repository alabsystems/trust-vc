::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: &'static R }
pub trait Tr2 { }
impl Tr2 for R { }
fn g<A: Tr2>(a: u8) -> u8 { a }
fn f() { let x = g::<R>(1); }
fn user() { assert(1 + 1 == 2); }
}
