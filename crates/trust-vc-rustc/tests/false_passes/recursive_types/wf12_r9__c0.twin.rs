::verus_builtin_macros::verus!{
pub struct R<'a> { pub a: u8, pub r: &'a u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
