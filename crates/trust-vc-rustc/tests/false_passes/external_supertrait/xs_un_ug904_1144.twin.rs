pub use self::Q as SubQ;
pub trait SubTr: Tr { }
verus!{
pub struct S<X> { pub x: X }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
impl Tr for u8 { }
impl<X: Q> Tr for S<X> { }
pub proof fn g<Y: SubQ + Tr>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { s.lm1(); }
pub trait Tr { }
pub trait Q { }
pub proof fn h<Y: SubQ + Tr>(s: S<Y>) ensures s.mm() == 2 { }
pub struct Z { pub z: u8 }
impl<X: Q> U for S<X> {
    proof fn lm0(&self) { }
    proof fn lm1(&self) where Self: Tr { }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl Q for Z { }
} // verus!
