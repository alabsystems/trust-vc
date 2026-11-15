::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external_body]
pub open spec fn e() -> bool {
    impl Drop for S { fn drop(&mut self) {} }
    true
}
fn user(s: S) -> T { s.t }

}
