verus!{
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
impl Q for B { }
pub struct Z { pub z: u8 }
pub proof fn fZ() { <Z as U<Z>>::lm0(&(Z { z: 0 })); }
impl U<Z> for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl Q for Z { }
pub struct B { pub b: u8 }
impl Tr for Z { }
pub struct A { pub a: u8 }
impl U<Z> for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub trait Q { }
impl U<B> for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
} // verus!
