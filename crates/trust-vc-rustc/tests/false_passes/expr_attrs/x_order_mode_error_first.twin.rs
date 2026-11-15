::verus_builtin_macros::verus!{
spec fn s() -> int { 1 }
fn f() { let a = s(); let y = 1u64; }
}
