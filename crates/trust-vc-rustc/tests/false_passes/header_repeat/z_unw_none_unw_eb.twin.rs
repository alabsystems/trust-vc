::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f()  { no_unwind(); opens_invariants_none(); }
fn user() { f();  }
}
