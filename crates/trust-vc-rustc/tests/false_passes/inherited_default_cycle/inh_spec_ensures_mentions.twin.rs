::verus_builtin_macros::verus!{
pub trait T {
    open spec fn h() -> int { 7 }
    fn g() -> (r: u8) ensures r == 7 { 7 }
}
pub struct S;
impl T for S {}
}
