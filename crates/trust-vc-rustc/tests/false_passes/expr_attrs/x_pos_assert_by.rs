::verus_builtin_macros::verus!{
proof fn g(x: int) { assert(x == x) by { let y = #[verifier::no_such_attribute] x; } }
}
