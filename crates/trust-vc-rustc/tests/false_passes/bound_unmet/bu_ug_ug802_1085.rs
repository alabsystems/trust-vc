verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
}
pub proof fn g<Y: Tr>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { s.lm0(); }
pub trait Q { }
impl<X> U for S<X> {
    fn z1(&self) -> (r: u8) where Self: Tr { 2 }
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl U for Z {
    fn z1(&self) -> (r: u8) { 2 }
    proof fn lm0(&self) { }
}
impl Q for u8 { }
impl Tr for u8 { }
pub trait Tr { }
} // verus!
