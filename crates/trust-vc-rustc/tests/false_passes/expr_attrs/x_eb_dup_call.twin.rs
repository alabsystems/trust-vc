::verus_builtin_macros::verus!{
fn e() {}
#[verifier::external_body]
fn f() { #[verifier::proof_note("a")] e(); }
}
