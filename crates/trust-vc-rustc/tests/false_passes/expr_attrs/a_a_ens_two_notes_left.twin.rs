::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verifier::custom_err("a")] r == 5 { 5 }
}
