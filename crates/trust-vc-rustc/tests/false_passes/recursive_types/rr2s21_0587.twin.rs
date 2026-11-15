::verus_builtin_macros::verus!{
pub struct S0<A: 'static> { pub f0: A, pub f1: &'static &'static u8 }
proof fn user() { }
}
