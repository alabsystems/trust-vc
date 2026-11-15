verus!{
pub fn fB() { let _r = <B as U<B>>::z1(&(B { b: 0 })); }
impl Tr for Z { }
impl U<Z> for A {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U<B> for B {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Q for B { }
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
impl Tr for B { }
pub struct A { pub a: u8 }
pub trait Tr { }
impl U<A> for Z {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
pub trait U<T> {
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
    proof fn rq0(&self) where T: Tr requires self.mm() == 2;
    open spec fn mm(&self) -> u8 { 2 }
}
pub fn fA() { let _r = <A as U<Z>>::z1(&(A { a: 0 })); }
} // verus!
