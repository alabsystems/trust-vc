::verus_builtin_macros::verus!{
pub struct S<T> { pub a: T }
pub trait Tr { }
impl<T: Copy> Tr for S<T> { }
fn f() { }
}
