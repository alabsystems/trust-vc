::verus_builtin_macros::verus!{
pub trait T { fn f(&self) -> (r: u8) ensures r == 1 { 1 } }
pub struct W<A> { pub v: A }
}
impl<A> T for W<A> { }
::verus_builtin_macros::verus!{
fn user(w: &W<u8>) { let r = 1u8; assert(r == 1); }
}
