::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { Some(1u8); }
fn user() { f(); }
}
