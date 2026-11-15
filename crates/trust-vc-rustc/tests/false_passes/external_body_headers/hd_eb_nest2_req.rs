::verus_builtin_macros::verus!{
fn g() {}
#[verifier::external_body]
fn f() { { requires(false); } let x: u8 = 5; }
fn user() { f(); }
}
