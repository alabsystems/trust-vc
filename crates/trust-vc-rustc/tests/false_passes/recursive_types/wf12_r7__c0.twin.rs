::verus_builtin_macros::verus!{
pub struct R(pub u8, pub &'static u8);
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
