::verus_builtin_macros::verus!{
fn g<T: Unpin>(t: T) { }
fn f() { g(1u8); }
}
