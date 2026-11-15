verus!{
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2 ensures true;
}
impl U for Z {
    proof fn rq1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
impl Q for u8 { }
pub struct Z { pub z: u8 }
pub trait Tr { }
} // verus!
