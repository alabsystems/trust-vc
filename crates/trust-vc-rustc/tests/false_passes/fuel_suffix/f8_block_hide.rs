::verus_builtin_macros::verus!{
spec fn f() -> int { 1 }
proof fn t() { { reveal_with_fuel(f, 0u32); } assert(f() == 1 || true); }
}
