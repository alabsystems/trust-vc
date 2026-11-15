::verus_builtin_macros::verus!{
pub struct S0;
#[verifier::external]
pub struct S1<A: 'static> { pub f0: A }
pub struct S2 { f0: &'static u8, pub f1: u8 }
pub trait Tr2 { }
impl Tr2 for S0 { }
proof fn pt(x: S0) { assert(x == x); }
proof fn user() { }
}
