verus!{
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait Q { }
impl Q for B { }
impl U for Z {
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Tr for Z { }
pub trait U {
    proof fn dd(&self) where Self: Tr + Q { self.lm1(); }
    fn z0(&self) -> (r: u8) where Self: Tr + Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr + Q { 2 }
    proof fn lm1(&self) where Self: Tr + Q ensures self.mm() == 2;
}
impl U for B {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
impl U for A {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub struct B { pub b: u8 }
} // verus!
