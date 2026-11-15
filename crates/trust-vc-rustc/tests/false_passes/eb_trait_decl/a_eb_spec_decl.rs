::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::external_body]
    spec fn s(&self) -> int;
}
pub struct S;
impl T for S { open spec fn s(&self) -> int { 1 } }
proof fn user() { assert(S.s() == 1); }
}
