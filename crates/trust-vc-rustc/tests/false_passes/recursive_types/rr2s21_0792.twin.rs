::verus_builtin_macros::verus!{
pub struct S0<A: 'static>(pub A, &'static u8, pub ());
pub struct S1<A: 'static>(pub A, nat);
pub trait Tr2 { }
impl Tr2 for S0<u8> { }
fn user() { assert(1 + 1 == 2); }
}
