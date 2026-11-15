::verus_builtin_macros::verus!{
pub struct S { pub x: u8 }
#[verifier::loop_isolation(false)]
fn user(s: S) -> (S, S) { let a = s; (a, s) }
}
