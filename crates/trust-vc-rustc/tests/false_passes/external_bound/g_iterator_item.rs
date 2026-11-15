::verus_builtin_macros::verus!{
fn count<I: Iterator<Item = u8>>(i: I) {}
fn f() { assert(1 + 1 == 2); }
}
