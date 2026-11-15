verus!{
pub trait Q { } impl Tr for Z { } impl Q for Z { }
pub proof fn g<Y: Tr>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { }
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
pub trait Tr { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub struct Z { pub z: u8 }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
