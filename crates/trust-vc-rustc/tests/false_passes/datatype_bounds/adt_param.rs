::verus_builtin_macros::verus!{
pub struct S<T: Unpin> { pub a: T }
fn f(s: S<u8>) { }
}
