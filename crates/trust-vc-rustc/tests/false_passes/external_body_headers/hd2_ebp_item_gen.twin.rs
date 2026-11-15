::verus_builtin_macros::verus!{
#[verifier(external_body)]
fn f<A>(a: &A) { fn inner() {}  }
fn user(x: u8) { f(&x); }
}
