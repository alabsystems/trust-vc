::verus_builtin_macros::verus!{
pub trait T {
    open spec fn g() -> int { S::h() + 1 }
    open spec fn h() -> int { 7 }
}
pub struct S;
impl T for S {}
proof fn p() { assert(S::g() == 8); }
}
