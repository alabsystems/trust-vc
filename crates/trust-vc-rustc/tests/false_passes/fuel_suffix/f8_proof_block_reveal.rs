::verus_builtin_macros::verus!{
spec fn f() -> int { 1 }
fn t() { proof { reveal_with_fuel(f, 1u32); } }
}
