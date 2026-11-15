::verus_builtin_macros::verus!{
pub trait T {
    proof fn g() ensures 1 + 1 == 2 { }
    proof fn h() ensures 1 + 1 == 2 { }
}
pub struct S;
impl T for S {}
}
