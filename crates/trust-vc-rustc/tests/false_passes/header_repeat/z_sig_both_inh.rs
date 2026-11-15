::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn f(&self) opens_invariants none no_unwind { opens_invariants_none(); no_unwind(); } }
fn user(s: &S) { s.f();  }
}
