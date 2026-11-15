::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() -> bool { let x: u8 = 5; ensures(true); true }
fn user() { let b = f(); }
}
