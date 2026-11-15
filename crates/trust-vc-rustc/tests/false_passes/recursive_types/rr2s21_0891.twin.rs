::verus_builtin_macros::verus!{
pub struct S0<A: 'static> { pub f0: A, pub f1: bool }
pub struct S1 { pub f0: int, pub f1: (&'static u8, bool), f2: u8 }
fn up(x: &S0<u8>) { }
impl S0<u8> { fn k() -> u8 { 1 } }
fn uk() { let x = S0::k(); }
fn user() { assert(1 + 1 == 2); }
}
