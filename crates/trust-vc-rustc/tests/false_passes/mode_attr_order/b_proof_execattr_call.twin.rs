::verus_builtin_macros::verus!{
#[verifier::proof]
proof fn q() ensures true { }
proof fn user() { q(); }
}
