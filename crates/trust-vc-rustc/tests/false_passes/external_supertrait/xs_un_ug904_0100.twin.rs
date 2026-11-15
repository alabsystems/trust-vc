pub use self::Q as SubQ;
pub trait SubTr: Tr { }
verus!{
pub struct S<X> { pub x: X }
impl U for Z {
    proof fn rq0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn rq0(&self) where Self: Q requires self.mm() == 2 ensures true;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub proof fn g<Y: SubQ + Tr>(s: S<Y>) where S<Y>: Q ensures s.mm() == 2 { }
impl<X: Q> U for S<X> {
    proof fn rq0(&self) where Self: Q { }
    fn z1(&self) -> (r: u8) { 2 }
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub trait Q { }
impl Q for Z { }
} // verus!
