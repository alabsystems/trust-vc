::verus_builtin_macros::verus!{
pub struct S<'a> { pub a: &'a u8 }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
