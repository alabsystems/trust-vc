::verus_builtin_macros::verus!{
spec fn f(x: u8) -> bool recommends x > 0 { recommends([x > 1]); true }
proof fn user() { assert(f(1)); }
}
