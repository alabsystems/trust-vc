verus!{
pub struct B { pub b: u8 }
pub struct Z { pub z: u8 }
impl U<B> for A {
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct A { pub a: u8 }
impl U<Z> for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub trait U<T> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) where T: Tr ensures r == self.mm();
}
pub trait Q { }
} // verus!
