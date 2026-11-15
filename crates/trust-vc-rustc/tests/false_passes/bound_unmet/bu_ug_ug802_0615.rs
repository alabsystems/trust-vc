verus!{
pub proof fn g<Y: Q>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { }
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
impl Tr for Z { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
impl U for Z {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
}
impl<X> U for S<X> {
    fn z0(&self) -> (r: u8) { 2 }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q { }
} // verus!
