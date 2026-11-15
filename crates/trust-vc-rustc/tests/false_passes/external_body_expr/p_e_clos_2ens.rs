::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|x: u8| { ensures(|r: u8| r > 0); ensures(|r: u8| r > 1); x }); }
fn user() { f(); }
}
