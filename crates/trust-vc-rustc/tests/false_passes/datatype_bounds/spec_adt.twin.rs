::verus_builtin_macros::verus!{
pub struct S<T> { pub a: T }
spec fn f(s: S<u8>) -> bool { true }
}
