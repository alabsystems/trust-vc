::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
macro_rules! mk { ($e:expr) => { { let s = crate::S { x: $e }; let a = s; let b = s; } } }
#[verifier::external_body]
fn e() { mk!(1); }
fn f() { let s = crate::S { x: 1 }; let a = s; }
fn g() { assert(1 + 1 == 2); }
}
