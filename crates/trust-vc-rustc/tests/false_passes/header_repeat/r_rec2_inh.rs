::verus_builtin_macros::verus!{
pub struct S {}
impl S { spec fn f(&self, x: u8) -> bool { recommends([x > 0]); recommends([x > 1]); true } }
proof fn user(s: &S) {{ assert(s.f(1)); }}
}
