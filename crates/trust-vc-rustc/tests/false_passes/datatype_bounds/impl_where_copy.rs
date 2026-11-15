::verus_builtin_macros::verus!{
pub struct S<T> { pub a: T }
pub trait Tr { fn m(&self); }
impl<T> Tr for S<T> where T: Copy { fn m(&self) {} }
fn f() { }
}
