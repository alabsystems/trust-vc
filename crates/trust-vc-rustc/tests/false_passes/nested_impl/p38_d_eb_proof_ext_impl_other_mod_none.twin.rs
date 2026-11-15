::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
proof fn e() {
    #[verifier::external]
    fn nested() {}
}
mod um { use super::*; pub fn user(s: S) -> T { s.t } }

}
