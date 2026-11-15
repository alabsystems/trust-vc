::verus_builtin_macros::verus!{
pub trait T {
    fn g() -> (r: u8) ensures r == 7 { 7 }
    fn h() -> (r: u8) ensures r == 7 { 7 }
}
pub struct W<A> { pub v: A }
impl<A> T for W<A> {}
}
