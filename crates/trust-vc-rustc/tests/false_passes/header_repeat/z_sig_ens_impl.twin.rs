::verus_builtin_macros::verus!{
pub trait T { fn f(&self); }
pub struct S {}
impl T for S { fn f(&self) ensures true { } }
fn user(s: &S) { s.f();  }
}
