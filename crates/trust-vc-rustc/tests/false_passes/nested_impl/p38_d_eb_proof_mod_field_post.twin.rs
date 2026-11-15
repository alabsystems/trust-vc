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
fn user(s: S) -> T { s.t }
fn g() -> (r: u8) ensures r == 2 { 1 }
}
