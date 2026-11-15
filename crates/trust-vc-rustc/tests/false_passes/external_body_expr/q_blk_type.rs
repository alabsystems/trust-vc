::verus_builtin_macros::verus!{
#[verifier::external]
fn g() -> fn() { h }
#[verifier::external]
fn h() {}
#[verifier::external_body]
fn f() { { g() }; }
fn user() { f(); }
}
