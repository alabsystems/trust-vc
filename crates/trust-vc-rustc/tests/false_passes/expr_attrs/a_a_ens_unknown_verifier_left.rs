::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verifier::no_such_attribute] r == 5 { 5 }
}
