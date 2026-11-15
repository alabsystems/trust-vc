::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() opens_invariants none no_unwind { }
fn user() { f();  }
}
