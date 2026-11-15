::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f()  { no_unwind(); no_unwind(); }
fn user() { f();  }
}
