::verus_builtin_macros::verus!{
proof fn t(tracked x: &mut u64) ensures *x == 5 { #[verifier::proof_note("m")] *x = 5; }
}
