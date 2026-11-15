::verus_builtin_macros::verus!{
fn g() {}
#[verifier::external_body]
fn f() { let mut x: u8 = 5; requires(false); }
fn user() { f(); }
}
