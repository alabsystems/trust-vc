pub trait SubQ: Q { }
verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm(&self) where Self: Tr ensures self.mm() == 2;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm(&self) { }
}
pub proof fn g<Y: Q>(s: S<Y>) ensures s.mm() == 2 { s.lm(); }
pub proof fn h<Y: SubQ>(s: S<Y>) ensures s.mm() == 2 { }
} // verus!
