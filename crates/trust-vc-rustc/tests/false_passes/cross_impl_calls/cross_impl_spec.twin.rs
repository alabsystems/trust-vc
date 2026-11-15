::verus_builtin_macros::verus!{
pub trait T {
    spec fn g(&self) -> int;
    spec fn h(&self) -> int;
}
pub struct S;
pub struct S2;
impl T for S { open spec fn g(&self) -> int { S2.h() } open spec fn h(&self) -> int { 7 } }
impl T for S2 { open spec fn g(&self) -> int { 7 } open spec fn h(&self) -> int { 7 } }
}
