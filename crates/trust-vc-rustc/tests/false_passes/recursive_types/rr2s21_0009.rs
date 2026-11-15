::verus_builtin_macros::verus!{
pub struct S0<A: 'static> { pub f0: A, pub f1: &'static S0<i32>, pub f2: u16 }
impl S0<u8> { fn k() -> u8 { 1 } }
fn uk() { let x = S0::k(); }
proof fn user() { }
}
