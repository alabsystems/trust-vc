::verus_builtin_macros::verus!{
pub struct S0 { f0: (&'static S0, &'static S0), f1: u8, pub f2: &'static S0 }
fn user() { assert(1 + 1 == 2); }
}
