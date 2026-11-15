::verus_builtin_macros::verus!{
pub struct S<T> { pub a: T }
pub struct R { pub s: S<u8> }
fn f() { }
}
