::verus_builtin_macros::verus!{
pub struct S {}
impl S { proof fn f(&self)  { requires([true]); ensures([true]); } }
proof fn user(s: &S) { s.f(); assert(false); }
}
