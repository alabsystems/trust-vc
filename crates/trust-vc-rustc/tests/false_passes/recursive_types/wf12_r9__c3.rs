::verus_builtin_macros::verus!{
pub struct R<'a> { pub a: u8, pub r: &'a R<'a> }
pub trait Tr2 { }
impl Tr2 for R<'static> { }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
