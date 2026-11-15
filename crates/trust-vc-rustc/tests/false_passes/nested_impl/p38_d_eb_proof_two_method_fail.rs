::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
proof fn e() {
    fn mid() { impl Drop for S { fn drop(&mut self) {} } }
}
impl S { fn take(self) -> T { self.t } }
fn g() { assert(1 + 1 == 3); }
}
