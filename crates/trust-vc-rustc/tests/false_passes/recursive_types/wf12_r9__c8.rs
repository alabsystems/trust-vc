::verus_builtin_macros::verus!{
pub struct R<'a> { pub a: u8, pub r: &'a R<'a> }
pub struct H { pub h: u8, pub k: &'static R<'static> }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
