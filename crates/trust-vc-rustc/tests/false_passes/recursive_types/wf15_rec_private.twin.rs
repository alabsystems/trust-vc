::verus_builtin_macros::verus!{
struct R { r: &'static u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
