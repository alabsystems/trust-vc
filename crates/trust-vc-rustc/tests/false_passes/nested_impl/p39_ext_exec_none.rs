::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
#[verifier::external]
fn e() {
    impl Drop for S { fn drop(&mut self) {} }
}
fn user(s: S) -> T { s.t }

}
