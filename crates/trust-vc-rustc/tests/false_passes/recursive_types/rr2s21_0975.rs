::verus_builtin_macros::verus!{
pub struct S0<A: 'static> { pub f0: &'static A, pub f1: (int, &'static S0<int>) }
fn user() { assert(1 + 1 == 2); }
}
