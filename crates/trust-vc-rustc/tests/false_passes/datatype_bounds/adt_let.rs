::verus_builtin_macros::verus!{
pub struct S<T: Unpin> { pub a: T }
fn f() { let s = S { a: 1u8 }; }
}
