::verus_builtin_macros::verus!{
pub struct S {}
impl S { #[verifier::external_body] pub uninterp spec fn f(&self) -> bool { recommends([true]); true } }
proof fn user(s: S) { assert(s.f() == s.f()); }
}
