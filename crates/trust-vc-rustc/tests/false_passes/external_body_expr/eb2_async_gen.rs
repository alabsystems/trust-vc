::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A) { async { }; }
fn user() {{ f(1u8); }}
}
