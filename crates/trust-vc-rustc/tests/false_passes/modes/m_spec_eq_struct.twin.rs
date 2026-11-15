::verus_builtin_macros::verus!{
struct S { a: u64 }
fn g(s: S, t: S) -> bool {
    s.a == t.a
}
}
