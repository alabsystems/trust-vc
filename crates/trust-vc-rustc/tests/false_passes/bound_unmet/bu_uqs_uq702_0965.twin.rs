verus!{
pub proof fn fA() { (A { a: 0 }).lm1(); }
impl Tr for B { }
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
pub trait Tr { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
impl Tr for A { }
impl Tr for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    proof fn dd(&self) where Self: Q { self.lm1(); }
}
pub struct Z { pub z: u8 }
pub trait Q: Tr { }
impl Q for A { }
} // verus!
