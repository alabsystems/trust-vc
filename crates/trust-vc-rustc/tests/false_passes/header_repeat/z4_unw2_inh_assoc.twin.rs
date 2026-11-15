::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f()  { no_unwind(); } }
fn user() { S::f();  }
}
