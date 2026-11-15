::verus_builtin_macros::verus!{
#[verus::internal(open)]
open spec fn s() -> int { 2 }
proof fn user() { assert(s() == 2); }
}
