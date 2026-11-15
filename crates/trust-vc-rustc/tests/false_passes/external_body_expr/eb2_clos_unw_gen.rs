::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f<A>(a: A) { (|x: u8| { no_unwind(); x }); }
fn user() {{ f(1u8); }}
}
