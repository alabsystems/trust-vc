verus!{
pub trait Tr { }
impl V for Z {
    proof fn lv(&self) { }
}
pub trait Q { }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub proof fn g<Y: Q>(s: S<Y>) where S<Y>: Tr ensures s.mm() == 2 { s.lm0(); }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl<X: Q> V for S<X> {
    proof fn lv(&self) { }
}
pub struct S<X> { pub x: X }
impl U for Z {
    proof fn lm0(&self) { }
}
} // verus!
