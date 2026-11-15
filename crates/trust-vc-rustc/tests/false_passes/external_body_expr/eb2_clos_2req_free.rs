::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|x: u8| { requires([x > 0]); requires([x > 1]); x }); }
fn user() {{ f(); }}
}
