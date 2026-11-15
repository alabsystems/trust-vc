::verus_builtin_macros::verus!{
struct S { a: u64 }
fn g() -> (r: u64)
    ensures r == 1
{
    let mut s = S { a: 0 };
    proof { s.a = 1; }
    s.a
}
}
