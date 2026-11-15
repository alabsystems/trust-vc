::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A) { (|x: &dyn Fn()| 0u8); }
fn user() {{ f(1u8); }}
}
