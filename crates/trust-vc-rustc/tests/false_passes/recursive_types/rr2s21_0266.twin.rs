::verus_builtin_macros::verus!{
pub struct S0<A: 'static>(A, pub &'static u8, i32);
impl S0<u8> { fn k() -> u8 { 1 } }
fn uk() { let x = S0::k(); }
fn user() { assert(1 + 1 == 2); }
}
