::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f(&self) no_unwind { no_unwind(); } }
fn user(s: &S) { s.f(); assert(false); }
}
