::verus_builtin_macros::verus!{
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
pub struct R { pub a: u8, pub r: &'static u8 }
