::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A) { (|x: u8| { requires([x > 0]); requires([x > 1]); x }); }
fn user() {{ f(1u8); }}
}
