pub use self::Q as SubQ;
pub trait SubTr: Tr { }
verus!{
impl<X> U for S<X> {
    proof fn rq0(&self) { }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl Tr for Z { }
pub struct Z { pub z: u8 }
impl<X> V for S<X> {
    proof fn lv(&self) { }
}
pub proof fn h<Y: SubQ>(s: S<Y>) ensures s.mm() == 2 { }
pub trait Tr { }
pub struct S<X> { pub x: X }
pub proof fn g<Y: SubQ>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq0(&self) where Self: Tr requires self.mm() == 2 ensures true;
}
impl Q for u8 { }
impl<X: Q> Tr for S<X> { }
pub trait Q { }
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl Q for Z { }
} // verus!
