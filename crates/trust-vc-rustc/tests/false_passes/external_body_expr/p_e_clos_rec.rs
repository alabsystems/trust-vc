::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|x: u8| { recommends(x > 0); x }); }
fn user() { f(); }
}
