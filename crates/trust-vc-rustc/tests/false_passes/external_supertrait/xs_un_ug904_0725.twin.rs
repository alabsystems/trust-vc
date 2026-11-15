pub use self::Q as SubQ;
pub trait SubTr: Tr { }
verus!{
impl U for Z {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr { }
}
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm0(&self) where Self: Tr { }
}
pub proof fn g<Y: SubQ>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { s.lm0(); }
pub proof fn h<Y: SubQ>(s: S<Y>) ensures s.mm() == 2 { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl Tr for Z { }
pub trait Q { }
} // verus!
