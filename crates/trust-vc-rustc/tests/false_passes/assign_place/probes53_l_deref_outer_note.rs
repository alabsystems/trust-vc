::verus_builtin_macros::verus!{
struct S { a: u64 }
fn mset(x: &mut u64) ensures *x == 7 { *x = 7; }
fn t(r: &mut u64) ensures *r == 5 { #[verifier::proof_note("m")] *r = 5; }
}
