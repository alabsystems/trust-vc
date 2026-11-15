::verus_builtin_macros::verus!{
pub trait T1 {
    fn h() -> (r: u8) ensures r == 7 { 7 }
    fn k() -> (r: u8) ensures r == 7 { S::g() }
}
pub trait T2 {
    fn g() -> (r: u8) ensures r == 7 { S::h() }
}
pub struct S;
impl T1 for S {}
impl T2 for S {}
}
