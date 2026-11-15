::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A)  { ensures([true]); no_unwind(); }
fn user() { f(1u8);  }
}
