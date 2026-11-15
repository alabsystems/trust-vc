::verus_builtin_macros::verus!{
struct S { x: u8 }
impl S {
#[verifier::external_body]
fn e(self) { let a = self; }
}
fn f() { assert(1 + 1 == 2); }
}
