::verus_builtin_macros::verus!{
fn f() -> (r: u64) ensures #[verus::proof_note("n")] r == 5 { 5 }
fn g() { let x = f(); assert(x == 5); }
}
