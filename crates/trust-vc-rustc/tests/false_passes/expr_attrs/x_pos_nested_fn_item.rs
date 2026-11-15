::verus_builtin_macros::verus!{
fn g() { #[verifier::no_such_attribute] fn h() {} }
}
