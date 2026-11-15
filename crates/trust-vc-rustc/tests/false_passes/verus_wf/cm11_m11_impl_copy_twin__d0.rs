::verus_builtin_macros::verus!{
#[verifier::external] pub struct S<T> { pub a: T }
pub trait Tr { }
impl<T> Tr for S<T> { }
fn f() { }
}
