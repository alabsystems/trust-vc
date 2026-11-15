verus!{
pub trait Q: Tr { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct A { pub a: u8 }
impl Tr for Z { }
impl U<Z> for Z {
    fn z1(&self) -> (r: u8) { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl U<Z> for A {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
pub struct B { pub b: u8 }
pub trait U<T> {
    open spec fn mm(&self) -> u8 where T: Tr + Q { 2 }
    fn z0(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
    fn z1(&self) -> (r: u8) where T: Tr + Q ensures r == self.mm();
}
} // verus!
