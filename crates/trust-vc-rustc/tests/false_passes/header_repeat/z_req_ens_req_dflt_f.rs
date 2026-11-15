::verus_builtin_macros::verus!{
pub trait T { fn f(&self)  { requires([true]); ensures([true]); requires([true]); } }
pub struct S {}
impl T for S {}
fn user(s: &S) { s.f(); assert(false); }
}
