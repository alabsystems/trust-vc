::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external]
spec fn e() -> bool {
    fn nested() {}
    true
}
fn user(s: S) -> T { s.t }
fn g() { assert(1 + 1 == 3); }
}
