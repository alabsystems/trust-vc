verus!{
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
pub struct A { pub a: u8 }
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 { 2 }
}
impl U for A {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl Q for A { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn dd(&self) where Self: Tr { self.lm0(); }
}
pub trait Tr { }
pub trait Q { }
impl Q for Z { }
} // verus!
