verus!{
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z(&self) -> (r: u8) ensures r == self.mm();
    fn dz(&self) -> (r: u8) { self.z() }
}
impl Tr for B { }
impl U<B> for A {
    fn z(&self) -> (r: u8) { 2 }
}
} // verus!
