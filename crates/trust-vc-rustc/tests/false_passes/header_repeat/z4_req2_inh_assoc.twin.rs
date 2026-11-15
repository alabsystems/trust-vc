::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f()  { requires([true]); } }
fn user() { S::f();  }
}
