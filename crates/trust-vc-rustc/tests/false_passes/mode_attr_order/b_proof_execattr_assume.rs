::verus_builtin_macros::verus!{
#[verifier::exec]
proof fn p() ensures false { assume(false); }
fn user() { p(); assert(false); }
}
