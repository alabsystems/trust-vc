::verus_builtin_macros::verus!{
proof fn g(x: int) { assert(#[verifier::no_such_attribute] (x == x)); }
}
