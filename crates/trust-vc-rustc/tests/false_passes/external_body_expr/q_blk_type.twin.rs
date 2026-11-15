::verus_builtin_macros::verus!{
#[verifier::external]
fn g() -> fn() { h }
#[verifier::external]
fn h() {}
#[verifier::external_body]
fn f() { { h() }; }
fn user() { f(); }
}
