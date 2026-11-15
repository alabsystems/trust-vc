::verus_builtin_macros::verus!{
pub struct R<'a> { pub a: u8, pub r: &'a u8 }
impl<'a> R<'a> { fn k() -> u8 { 1 } }
fn f() { let x = R::k(); }
fn user() { assert(1 + 1 == 2); }
}
