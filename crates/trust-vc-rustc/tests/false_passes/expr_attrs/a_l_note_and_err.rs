::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verifier::proof_note("n")] #[verifier::custom_err("c")] r == 5 { 5 }
fn g() { let x = f(); assert(x == 5); }
}
