::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let y: u8 = 1; proof { requires(false); } }
fn user() { f(); }
}
