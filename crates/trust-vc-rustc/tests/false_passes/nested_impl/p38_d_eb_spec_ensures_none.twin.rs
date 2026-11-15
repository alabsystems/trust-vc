::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
spec fn e() -> bool {
    fn nested() {}
    true
}
fn user(s: S) -> (r: T) ensures r.y == s.t.y { s.t }

}
