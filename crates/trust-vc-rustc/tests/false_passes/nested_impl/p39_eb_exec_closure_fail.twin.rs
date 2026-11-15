::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
fn e() {
    let c = || { fn nested() {} };
}
fn user(s: S) -> T { s.t }
fn g() { assert(1 + 1 == 3); }
}
