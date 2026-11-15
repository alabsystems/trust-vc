::verus_builtin_macros::verus!{
struct S { x: u8 }
#[verifier::external]
fn e() { let s = S { x: 1 }; let a = s; let b = s; }
fn f() { assert(1 + 1 == 2); }
}
