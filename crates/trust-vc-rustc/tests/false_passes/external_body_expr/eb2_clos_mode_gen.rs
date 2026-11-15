::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A) { (|#[verifier::proof] x: u8| x); }
fn user() {{ f(1u8); }}
}
