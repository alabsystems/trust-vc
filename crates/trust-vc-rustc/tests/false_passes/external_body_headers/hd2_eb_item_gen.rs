::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: &A) { fn inner() {} requires(false); }
fn user(x: u8) { f(&x); }
}
