verus!{
impl V for Z {
    proof fn lv(&self) { }
}
impl U for Z {
    proof fn rq1(&self) { }
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn rq1(&self) where Self: Tr requires self.mm() == 2 ensures true;
}
impl<X> U for S<X> {
    proof fn lm0(&self) { }
    open spec fn mm(&self) -> u8 { 2 }
    proof fn rq1(&self) { }
}
pub trait Tr { }
pub struct S<X> { pub x: X }
impl Q for Z { }
impl<X: Q> Tr for S<X> { }
impl<X: Q> V for S<X> {
    proof fn lv(&self) { }
}
pub trait Q { }
impl Tr for u8 { }
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
} // verus!
