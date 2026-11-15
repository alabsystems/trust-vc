::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::spec]
    spec fn s(&self) -> bool;
}
pub struct S;
impl T for S { open spec fn s(&self) -> bool { true } }
proof fn user() { assert(S.s()); }
}
