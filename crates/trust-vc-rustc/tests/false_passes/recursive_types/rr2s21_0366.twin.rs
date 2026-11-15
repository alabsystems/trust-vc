::verus_builtin_macros::verus!{
pub struct S0 { f0: (&'static u8, &'static u8), f1: u8, pub f2: &'static u8 }
fn user() { assert(1 + 1 == 2); }
}
