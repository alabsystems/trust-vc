::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub r: (u8, &'static R) }
impl R { fn k() -> u8 { 1 } }
fn f() { let x = R::k(); }
fn user() { assert(1 + 1 == 2); }
}
