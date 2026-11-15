::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A)  { opens_invariants_none(); no_unwind(); opens_invariants_none(); }
fn user() { f(1u8);  }
}
