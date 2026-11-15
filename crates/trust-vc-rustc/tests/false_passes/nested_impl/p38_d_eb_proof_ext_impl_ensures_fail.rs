::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
proof fn e() {
    #[verifier::external]
    impl Drop for S { fn drop(&mut self) {} }
}
fn user(s: S) -> (r: T) ensures r.y == s.t.y { s.t }
fn g() { assert(1 + 1 == 3); }
}
