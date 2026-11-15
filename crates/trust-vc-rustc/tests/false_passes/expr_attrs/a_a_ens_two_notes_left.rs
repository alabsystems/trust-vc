::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verifier::custom_err("a")] #[verifier::custom_err("b")] r == 5 { 5 }
}
