::verus_builtin_macros::verus!{
pub trait T {
    fn g() -> (r: u8) ensures r == 7 { helper() }
    fn h() -> (r: u8) ensures r == 7 { 7 }
}
pub struct S;
impl T for S {}
fn helper() -> (r: u8) ensures r == 7 { S::h() }
}
