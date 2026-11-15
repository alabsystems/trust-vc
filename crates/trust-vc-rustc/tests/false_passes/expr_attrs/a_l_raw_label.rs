::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verifier::proof_note(r"n")] r == 5 { 5 }
fn g() { let x = f(); assert(x == 5); }
}
