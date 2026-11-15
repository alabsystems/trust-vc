::verus_builtin_macros::verus!{
pub struct S0((&'static bool, &'static S0));
fn user() { assert(1 + 1 == 2); }
}
