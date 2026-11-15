verus!{
pub trait Q { }
pub struct B { pub b: u8 }
pub struct A { pub a: u8 }
pub struct Z { pub z: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where T: Tr + Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
}
impl U<Z> for A {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
pub trait Tr { }
impl U<Z> for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl U<B> for B {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl Q for B { }
} // verus!
