::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
proof fn e() {
    #[verifier::external]
    fn nested() {}
}
fn user(s: S) -> T { s.t }
fn g() -> (r: u8) ensures r == 2 { 1 }
}
