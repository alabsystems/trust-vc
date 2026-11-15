::verus_builtin_macros::verus!{
pub struct S0 { f0: (), pub f1: (char, &'static u8), f2: &'static u8 }
pub trait Tr2 { }
impl Tr2 for S0 { }
spec fn sid<B>(a: int) -> int { a }
proof fn us() { assert(sid::<S0>(1) == 1); }
fn user() { assert(1 + 1 == 2); }
}
