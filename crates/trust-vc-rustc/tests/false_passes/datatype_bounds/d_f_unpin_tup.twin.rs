::verus_builtin_macros::verus!{
pub trait Tr { }
impl Tr for u8 { }
#[verifier::external]
pub trait Ex { }
#[verifier::external]
impl Ex for u8 { }
fn g<T>(t: T) { }
fn f(a: (u8, u8)) { g(a); }
}
