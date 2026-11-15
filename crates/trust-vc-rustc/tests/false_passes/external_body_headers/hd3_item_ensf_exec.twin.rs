::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() -> bool { fn inner() {} true }
fn user() { let b = f(); }
}
