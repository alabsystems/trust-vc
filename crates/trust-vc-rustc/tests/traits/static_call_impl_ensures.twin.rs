::verus_builtin_macros::verus!{
trait T {
    fn m(&self) -> (r: u8)
        ensures r > 0;
}
struct S {}
impl T for S {
    fn m(&self) -> (r: u8)
        ensures r == 7
    {
        7
    }
}
fn test<A: T>(s: A) {
    let x = s.m();
    assert(x == 7);
}
}
