::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() ensures true { ensures([true]); }
fn user() { f();  }
}
