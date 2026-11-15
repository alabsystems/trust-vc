::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f()  { ensures([true]); no_unwind(); }
fn user() { f();  }
}
