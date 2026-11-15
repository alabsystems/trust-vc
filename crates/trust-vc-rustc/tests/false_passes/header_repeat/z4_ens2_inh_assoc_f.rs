::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f()  { ensures([true]); ensures([true]); } }
fn user() { S::f(); assert(false); }
}
