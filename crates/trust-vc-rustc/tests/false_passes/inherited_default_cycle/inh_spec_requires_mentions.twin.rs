::verus_builtin_macros::verus!{
pub trait T {
    open spec fn h() -> int { 7 }
    fn g(x: u8) requires x == 7 { }
}
pub struct S;
impl T for S {}
}
