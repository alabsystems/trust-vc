::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() -> bool { fn inner() {} ensures(true); true }
fn user() { let b = f(); }
}
