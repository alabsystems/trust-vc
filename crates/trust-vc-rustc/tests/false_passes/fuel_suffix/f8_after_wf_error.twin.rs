::verus_builtin_macros::verus!{
spec fn f() -> int { 1 }
proof fn t0() { assert(true); hide(f); }
proof fn t() { reveal_with_fuel(f, 1); }
}
