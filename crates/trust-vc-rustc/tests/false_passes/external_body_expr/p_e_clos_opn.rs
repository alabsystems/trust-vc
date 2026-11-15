::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|x: u8| { opens_invariants_none(); x }); }
fn user() { f(); }
}
