::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let y: u8 = 1; }
fn user() { f(); }
}
