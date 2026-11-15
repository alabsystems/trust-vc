::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::external_body]
fn e() { fn inner() { let s = crate::S { x: 1 }; let a = s; } }
fn g() { assert(1 + 1 == 3); }
}
