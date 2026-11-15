::verus_builtin_macros::verus!{
trait T {
    fn m(&self, x: u8)
        requires x > 5;
}
struct S {}
impl T for S {
    fn m(&self, x: u8) {}
}
fn test(s: S) {
    s.m(3);
}
}
