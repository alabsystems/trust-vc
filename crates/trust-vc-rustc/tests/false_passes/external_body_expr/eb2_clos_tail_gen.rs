::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A) { (|x: u8| { requires([x > 0]) }); }
fn user() {{ f(1u8); }}
}
