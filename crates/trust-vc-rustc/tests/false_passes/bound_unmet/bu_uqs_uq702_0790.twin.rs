verus!{
pub trait Tr { } impl Tr for Z { } impl Q for Z { }
impl Q for B { }
pub struct Z { pub z: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub struct B { pub b: u8 }
impl Tr for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
impl Tr for B { }
impl Q for A { }
pub trait Q: Tr { }
pub struct A { pub a: u8 }
impl U for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
} // verus!
