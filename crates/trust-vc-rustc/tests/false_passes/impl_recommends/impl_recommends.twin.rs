::verus_builtin_macros::verus!{
pub trait T { spec fn f(&self, x: nat) -> nat; }
pub struct S;
impl T for S { open spec fn f(&self, x: nat) -> nat { x } }
}
