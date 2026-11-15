::verus_builtin_macros::verus!{
#[verifier::exec]
proof fn q() ensures true { }
proof fn user() { q(); }
}
