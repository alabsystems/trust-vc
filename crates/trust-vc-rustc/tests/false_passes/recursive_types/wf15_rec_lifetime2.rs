::verus_builtin_macros::verus!{
pub struct R<'a, 'b> { pub a: &'a u8, pub r: &'b R<'a, 'b> }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
