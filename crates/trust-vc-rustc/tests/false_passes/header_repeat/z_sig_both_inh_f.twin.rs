::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f(&self) opens_invariants none no_unwind { } }
fn user(s: &S) { s.f(); assert(false); }
}
