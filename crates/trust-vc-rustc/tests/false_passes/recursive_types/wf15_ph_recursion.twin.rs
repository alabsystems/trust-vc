::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: &'static u8 }
spec fn s(x: int) -> int { s(x) }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
