::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: &A) { let x: u8 = 5;  }
fn user(x: u8) { f(&x); }
}
