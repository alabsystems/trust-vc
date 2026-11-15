::verus_builtin_macros::verus!{
pub trait Tr { }
impl Tr for u8 { }
#[verifier::external]
pub trait Ex { }
#[verifier::external]
impl Ex for u8 { }
pub struct S<T: core::fmt::Debug> { pub a: T }
spec fn f(s: S<(u8, u8)>) -> bool { true }
}
