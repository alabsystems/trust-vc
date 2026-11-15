::verus_builtin_macros::verus!{
pub struct R<'a, 'b> { pub a: &'a u8, pub r: &'b u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
