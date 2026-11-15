verus!{
pub struct A { pub a: u8 }
pub struct B;
pub trait Tr {
    spec fn lim(&self) -> u8;
    fn step(&self, i: u8) -> (r: u8)
        requires i < self.lim(),
        ensures r == i + 1;
    fn lim_e(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> (r: u8)

    {
        let n = self.lim_e();
        let mut i: u8 = 0;
        loop
            invariant_except_break i <= n, n == self.lim(),
            ensures i == n,
            decreases n - i,
        {
            if i >= n { break; }
            i = self.step(i);
        }
        i
    }
}
impl Tr for A {
    open spec fn lim(&self) -> u8 { self.a }
    fn step(&self, i: u8) -> (r: u8) { i + 1 }
    fn lim_e(&self) -> (r: u8) { self.a }
}
fn user0() {
    let v = A { a: 2 };
    let r = v.run();
    assert(r == 2);
}
} // verus!
