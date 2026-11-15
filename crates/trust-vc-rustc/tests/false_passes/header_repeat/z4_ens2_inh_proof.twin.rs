::verus_builtin_macros::verus!{
pub struct S {}
impl S { proof fn f(&self)  { ensures([true]); } }
proof fn user(s: &S) { s.f();  }
}
