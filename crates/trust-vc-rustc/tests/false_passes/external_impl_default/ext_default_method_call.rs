::verus_builtin_macros::verus!{
pub trait T { fn f(&self) -> (r: u8) ensures r == 1 { 1 } }
pub struct S;
}
impl T for S { }
::verus_builtin_macros::verus!{
fn user(s: &S) { let r = s.f(); assert(r == 1); }
}
