::verus_builtin_macros::verus!{
struct S { a: u64 }
fn mset(x: &mut u64) ensures *x == 7 { *x = 7; }
proof fn t() { let mut g: int = 0; g = 5; assert(g == 5); }
}
