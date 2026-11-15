::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: &'static u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
