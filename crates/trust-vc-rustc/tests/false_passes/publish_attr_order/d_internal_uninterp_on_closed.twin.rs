::verus_builtin_macros::verus!{
#[verus::internal(uninterp)]
uninterp spec fn s() -> int { 2 }
proof fn user() { assert(s() == 2); }
}
