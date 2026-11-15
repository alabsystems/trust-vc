::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
impl T {
#[verifier::external_body]
proof fn e() {
    fn nested() {}
}
}
impl S { fn take(self) -> T { self.t } }
fn g() { assert(1 + 1 == 3); }
}
