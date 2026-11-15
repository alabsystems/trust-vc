::verus_builtin_macros::verus!{
pub struct S<T: Copy> { pub a: T }
fn f(s: S<u8>) { }
}
