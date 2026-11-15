::verus_builtin_macros::verus!{
pub trait T {
    fn g(&self) -> (r: u8) ensures r == 7;
    fn h(&self) -> (r: u8) ensures r == 7;
}
pub struct S;
pub struct S2;
impl T for S { fn g(&self) -> (r: u8) { let s = S2; s.h() } fn h(&self) -> (r: u8) { 7 } }
impl T for S2 { fn g(&self) -> (r: u8) { 7 } fn h(&self) -> (r: u8) { 7 } }
}
