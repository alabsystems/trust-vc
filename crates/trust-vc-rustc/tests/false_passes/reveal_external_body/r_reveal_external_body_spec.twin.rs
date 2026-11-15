::verus_builtin_macros::verus!{
#[verifier::opaque]
spec fn s(a: bool) -> bool { a }
proof fn foo() { reveal(s); }
}
