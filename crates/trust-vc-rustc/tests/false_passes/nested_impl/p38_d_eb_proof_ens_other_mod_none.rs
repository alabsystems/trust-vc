::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
proof fn e(a: int) -> (r: int)
    requires a > 0
    ensures r == a
{
    impl Drop for S { fn drop(&mut self) {} }
    a
}
mod um { use super::*; pub fn user(s: S) -> T { s.t } }

}
