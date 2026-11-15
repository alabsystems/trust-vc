::verus_builtin_macros::verus!{
struct S { f: u64, g: u64 }
fn test() -> (r: u64) ensures r == 1 { let mut s = S { f: 0, g: 0 }; s.f += 1; s.f }
}
