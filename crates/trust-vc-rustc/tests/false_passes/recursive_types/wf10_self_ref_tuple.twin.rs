::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: (u8, &'static u8) }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
