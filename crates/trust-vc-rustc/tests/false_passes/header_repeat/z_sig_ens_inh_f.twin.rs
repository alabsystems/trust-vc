::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f(&self) ensures true { } }
fn user(s: &S) { s.f(); assert(false); }
}
