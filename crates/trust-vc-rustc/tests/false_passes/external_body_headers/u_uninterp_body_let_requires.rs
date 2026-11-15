::verus_builtin_macros::verus!{
#[verifier::external_body]
pub uninterp spec fn f(x: int) -> bool { let y: u8 = 5; requires(x > 0); true }
proof fn user() { assert(f(1) == f(1)); }
}
