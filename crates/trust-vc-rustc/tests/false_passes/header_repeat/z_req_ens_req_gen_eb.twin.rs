::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A)  { requires([true]); ensures([true]); }
fn user() { f(1u8);  }
}
