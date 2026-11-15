::verus_builtin_macros::verus!{
pub struct S0<A: 'static> { f0: A }
pub struct S1<A: 'static> { pub f0: (u8, A), f1: &'static S0<u8>, f2: &'static S2<S1<bool>> }
pub struct S2<A: 'static> { f0: &'static A }
impl S1<u8> { fn k() -> u8 { 1 } }
fn uk() { let x = S1::k(); }
proof fn user() { }
}
