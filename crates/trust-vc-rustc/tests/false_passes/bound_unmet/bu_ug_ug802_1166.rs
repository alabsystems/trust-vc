verus!{
impl<X: Q> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) { }
}
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
pub trait Q { }
impl V for Z {
    proof fn lv(&self) { }
}
pub struct S<X> { pub x: X }
impl<X: Q> V for S<X> {
    proof fn lv(&self) { }
}
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
} // verus!
