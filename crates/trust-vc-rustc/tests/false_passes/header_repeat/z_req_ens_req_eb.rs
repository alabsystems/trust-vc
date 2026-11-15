::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f()  { requires([true]); ensures([true]); requires([true]); }
fn user() { f();  }
}
