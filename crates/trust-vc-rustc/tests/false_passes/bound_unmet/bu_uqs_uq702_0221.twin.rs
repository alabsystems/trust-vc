verus!{
impl U for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl Tr for A { }
pub struct B { pub b: u8 }
pub trait Q { }
pub proof fn fA() { (A { a: 0 }).lm0(); }
impl U for B {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Q for B { }
impl Tr for Z { }
impl Q for Z { }
pub trait U {
    open spec fn mm(&self) -> u8 { 2 }
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
} // verus!
