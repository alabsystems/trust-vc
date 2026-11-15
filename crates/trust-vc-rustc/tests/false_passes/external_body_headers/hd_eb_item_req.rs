::verus_builtin_macros::verus!{
fn g() {}
#[verifier::external_body]
fn f() { fn inner() {} requires(false); }
fn user() { f(); }
}
