::verus_builtin_macros::verus!{
pub trait Tr { }
impl Tr for u8 { }
#[verifier::external]
pub trait Ex { }
#[verifier::external]
impl Ex for u8 { }
pub struct S<T: Copy> { pub a: T }
fn f(s: S<u8>) { }
}
