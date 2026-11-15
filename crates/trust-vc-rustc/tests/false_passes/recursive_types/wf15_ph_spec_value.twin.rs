::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: &'static u8 }
spec fn s(r: R) -> u8 { r.a }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
