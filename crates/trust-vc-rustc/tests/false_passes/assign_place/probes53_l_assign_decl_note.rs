::verus_builtin_macros::verus!{
struct S { a: u64 }
fn mset(x: &mut u64) ensures *x == 7 { *x = 7; }
fn t() { let x: u64; #[verifier::proof_note("m")] x = 5; assert(x == 5); }
}
