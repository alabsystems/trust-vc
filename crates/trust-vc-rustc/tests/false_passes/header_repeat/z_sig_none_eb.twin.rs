::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() opens_invariants none { }
fn user() { f();  }
}
