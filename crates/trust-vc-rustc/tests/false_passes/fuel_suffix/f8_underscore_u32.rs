::verus_builtin_macros::verus!{
spec fn f() -> int { 1 }
proof fn t() { hide(f); reveal_with_fuel(f, 1_u32); assert(f() == 1); }
}
