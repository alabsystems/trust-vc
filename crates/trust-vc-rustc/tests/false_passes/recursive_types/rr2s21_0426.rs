::verus_builtin_macros::verus!{
pub struct S0 {  }
pub struct S1<A: 'static> { f0: (u8, A), pub f1: &'static S1<&'static S0> }
pub struct S2<A: 'static>(pub (u8, A), pub nat);
proof fn user() { }
}
