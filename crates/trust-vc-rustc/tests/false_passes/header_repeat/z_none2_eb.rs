::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f()  { opens_invariants_none(); opens_invariants_none(); }
fn user() { f();  }
}
