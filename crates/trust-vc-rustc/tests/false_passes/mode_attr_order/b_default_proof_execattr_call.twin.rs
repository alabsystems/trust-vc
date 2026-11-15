::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::proof]
    proof fn q(&self) ensures true { }
}
pub struct S;
impl T for S { }
proof fn user() { S.q(); }
}
