::verus_builtin_macros::verus!{
pub struct S0 { pub f0: &'static S0 }
impl S0 { fn k() -> u8 { 1 } }
fn uk() { let x = S0::k(); }
fn ul() -> u8 { 1 }
fn user() { assert(1 + 1 == 2); }
}
