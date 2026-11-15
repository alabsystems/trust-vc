::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: &'static u8 }
spec fn s() -> int { 1 }
fn f() { let x: int = s(); }
fn user() { assert(1 + 1 == 2); }
}
