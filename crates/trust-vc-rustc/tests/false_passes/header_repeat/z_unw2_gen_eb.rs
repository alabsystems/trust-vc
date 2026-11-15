::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A)  { no_unwind(); no_unwind(); }
fn user() { f(1u8);  }
}
