::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f()  { opens_invariants_none(); } }
fn user() { S::f(); assert(false); }
}
