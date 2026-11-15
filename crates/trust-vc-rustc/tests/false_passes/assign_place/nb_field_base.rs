::verus_builtin_macros::verus!{
struct S { a: u64 }
fn t() { let mut s = S { a: 0 }; (#[verifier::proof_note("m")] s).a = 5; assert(s.a == 5); }
}
