::verus_builtin_macros::verus!{
pub struct S0<A: 'static> { pub f0: A, pub f1: nat, f2: &'static S0<&'static nat> }
pub struct S1 { f0: &'static char }
pub struct S2;
proof fn pt(x: S2) { assert(x == x); }
fn user() { assert(1 + 1 == 2); }
}
