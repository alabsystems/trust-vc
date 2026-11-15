::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { { <(u8, u8) as Clone>::clone }; }
fn user() { f(); }
}
