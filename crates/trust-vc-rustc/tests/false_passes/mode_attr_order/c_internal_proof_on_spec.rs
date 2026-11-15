::verus_builtin_macros::verus!{
#[verus::internal(proof)]
spec fn s() -> bool { false }
proof fn user() { let b = s(); assert(!b); }
}
