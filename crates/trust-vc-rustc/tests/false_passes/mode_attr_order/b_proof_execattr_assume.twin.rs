::verus_builtin_macros::verus!{
#[verifier::proof]
proof fn p() ensures false { assume(false); }
fn user() { p(); assert(false); }
}
