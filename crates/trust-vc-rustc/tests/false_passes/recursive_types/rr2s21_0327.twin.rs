::verus_builtin_macros::verus!{
pub struct S0((&'static bool, &'static u8));
fn user() { assert(1 + 1 == 2); }
}
