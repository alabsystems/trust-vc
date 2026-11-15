::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f(&self)  { requires([true]); ensures([true]); } }
fn user(s: &S) { s.f();  }
}
