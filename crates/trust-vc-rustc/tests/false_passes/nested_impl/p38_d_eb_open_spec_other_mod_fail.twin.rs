::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
pub open spec fn e() -> bool {
    fn nested() {}
    true
}
mod um { use super::*; pub fn user(s: S) -> T { s.t } }
fn g() { assert(1 + 1 == 3); }
}
