pub trait SubQ: Q { }
pub trait SubTr: Tr { }
verus!{
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr { 2 }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub proof fn g<Y: SubQ + Tr>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { }
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
pub trait Q { }
pub struct Z { pub z: u8 }
} // verus!
