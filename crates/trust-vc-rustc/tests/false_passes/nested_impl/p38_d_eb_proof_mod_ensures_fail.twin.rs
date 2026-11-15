::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
mod m {
use super::*;
#[verifier::external_body]
pub proof fn e() {
    fn nested() {}
}
}
fn user(s: S) -> (r: T) ensures r.y == s.t.y { s.t }
fn g() { assert(1 + 1 == 3); }
}
