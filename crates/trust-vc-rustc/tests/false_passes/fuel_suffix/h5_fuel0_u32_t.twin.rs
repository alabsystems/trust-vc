::verus_builtin_macros::verus!{
spec fn f() -> int { 1 }
spec fn g() -> int { f() }
proof fn t() { reveal_with_fuel(f, 0); assert(f() == 1 || true); }
}
