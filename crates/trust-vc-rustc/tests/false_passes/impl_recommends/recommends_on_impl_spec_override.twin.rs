::verus_builtin_macros::verus!{
pub trait T { open spec fn f(&self, x: nat) -> nat { x } }
pub struct S;
impl T for S { open spec fn f(&self, x: nat) -> nat { x + 1 } }
}
