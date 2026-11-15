::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verifier::truncate] r == 5 { 5 }
}
