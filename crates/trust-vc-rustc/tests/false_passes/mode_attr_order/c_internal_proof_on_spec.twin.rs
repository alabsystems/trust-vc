::verus_builtin_macros::verus!{
#[verus::internal(spec)]
spec fn s() -> bool { false }
proof fn user() { let b = s(); assert(!b); }
}
