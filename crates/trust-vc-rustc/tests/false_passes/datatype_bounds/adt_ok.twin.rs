::verus_builtin_macros::verus!{
pub struct S<T> { pub a: T }
fn f(s: S<u8>) { }
}
