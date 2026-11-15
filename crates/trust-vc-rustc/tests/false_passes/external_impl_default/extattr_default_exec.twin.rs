::verus_builtin_macros::verus!{
pub trait T { fn f(&self) -> (r: u8) ensures r == 1 { 1 } }
pub struct S;
#[allow(dead_code)]
impl T for S { }
fn user(s: &S) { let r = s.f(); assert(r == 1); }
}
