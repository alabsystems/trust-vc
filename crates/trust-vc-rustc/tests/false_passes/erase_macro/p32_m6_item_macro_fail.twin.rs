::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external_body]
fn e() {
} macro_rules! mkfn { () => { fn h() { let s = crate::S { x: 1 }; let a = s; } } }
mkfn!();
fn g() { assert(1 + 1 == 3); }
}
