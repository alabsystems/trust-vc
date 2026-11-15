::verus_builtin_macros::verus!{
mod m { pub open spec fn f() -> int { 1 } }
proof fn t() { reveal_with_fuel(m::f, 1u32); assert(m::f() == 1); }
}
