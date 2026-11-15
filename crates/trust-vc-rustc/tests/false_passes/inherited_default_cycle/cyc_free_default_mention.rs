::verus_builtin_macros::verus!{
pub trait T {
    open spec fn h(&self) -> int { 7 }
    open spec fn g(&self) -> int { helper() }
}
pub struct S;
impl T for S {}
pub open spec fn helper() -> int { S.h() }
}
