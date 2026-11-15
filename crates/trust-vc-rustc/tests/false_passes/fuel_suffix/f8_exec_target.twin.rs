::verus_builtin_macros::verus!{
fn g() {}
proof fn t() { reveal_with_fuel(g, 1); }
}
