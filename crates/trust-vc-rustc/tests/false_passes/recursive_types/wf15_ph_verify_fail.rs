::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: &'static R }
fn f() { assert(1 + 1 == 3); }
fn user() { assert(1 + 1 == 2); }
}
