::verus_builtin_macros::verus!{
pub struct S {}
impl S { proof fn f(&self) requires true { requires([true]); } }
proof fn user(s: &S) { s.f(); assert(false); }
}
