::verus_builtin_macros::verus!{
pub trait T { spec fn f(&self, x: nat) -> nat; }
pub struct W<A> { pub v: A }
impl<A> T for W<A> { open spec fn f(&self, x: nat) -> nat { x } }
}
