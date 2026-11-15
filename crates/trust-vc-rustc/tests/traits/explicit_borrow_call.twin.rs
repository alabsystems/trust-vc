::verus_builtin_macros::verus!{
trait T {
    fn m(s: &Self) -> (r: bool)
        ensures r;
}
struct S {}
impl T for S {
    fn m(s: &Self) -> (r: bool) { true }
}
fn test(s: S) {
    let b = S::m(&s);
    assert(!b);
}
}
