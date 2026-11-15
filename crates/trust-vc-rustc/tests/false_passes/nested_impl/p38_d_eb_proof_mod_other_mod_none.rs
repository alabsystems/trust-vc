::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
mod m {
use super::*;
#[verifier::external_body]
pub proof fn e() {
    impl Drop for S { fn drop(&mut self) {} }
}
}
mod um { use super::*; pub fn user(s: S) -> T { s.t } }

}
