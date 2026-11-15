::verus_builtin_macros::verus!{
pub trait Tr { }
impl Tr for u8 { }
#[verifier::external]
pub trait Ex { }
#[verifier::external]
impl Ex for u8 { }
spec fn g<T: Unpin>(t: T) -> bool { true }
spec fn f(a: u8) -> bool { g(a) }
}
