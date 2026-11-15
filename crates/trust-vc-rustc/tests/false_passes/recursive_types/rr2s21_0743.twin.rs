::verus_builtin_macros::verus!{
pub struct S0 { pub f0: &'static u8 }
pub struct S1 {  }
pub struct S2<A: 'static>(pub A);
proof fn pt(x: S1) { assert(x == x); }
fn ul() -> u8 { 1 }
fn user() { assert(1 + 1 == 2); }
}
