::verus_builtin_macros::verus!{
pub trait T {
    fn g(&self) -> (r: u8) ensures r == 7 { let s = S; s.h() }
    fn h(&self) -> (r: u8) ensures r == 7 { 7 }
}
pub struct S;
impl T for S {}
}
