::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
proof fn test() { { broadcast use f; } assert(f()); }
}
