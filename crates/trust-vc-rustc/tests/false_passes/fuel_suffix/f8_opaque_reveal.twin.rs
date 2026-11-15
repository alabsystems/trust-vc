::verus_builtin_macros::verus!{
#[verifier::opaque]
spec fn o() -> int { 1 }
proof fn t() { reveal_with_fuel(o, 1); assert(o() == 1); }
}
