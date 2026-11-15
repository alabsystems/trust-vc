::verus_builtin_macros::verus!{
pub struct S0<A: 'static> { f0: A, f1: &'static S0<&'static int> }
fn user() { assert(1 + 1 == 2); }
}
