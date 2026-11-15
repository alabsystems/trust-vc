::verus_builtin_macros::verus!{
fn t(r: &mut u64) ensures *r == 6 { *#[verifier::proof_note("m")] r = 5; }
}
