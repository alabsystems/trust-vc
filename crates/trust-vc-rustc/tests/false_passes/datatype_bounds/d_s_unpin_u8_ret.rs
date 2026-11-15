::verus_builtin_macros::verus!{
pub trait Tr { }
impl Tr for u8 { }
#[verifier::external]
pub trait Ex { }
#[verifier::external]
impl Ex for u8 { }
pub struct S<T: Unpin> { pub a: T }
fn f(a: u8) -> S<u8> { S { a } }
}
