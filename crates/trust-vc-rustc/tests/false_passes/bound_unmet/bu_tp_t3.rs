verus!{
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Tr { }
pub trait V<T> {
    open spec fn dv(&self) -> u8 where T: Tr { 5 }
    proof fn lv(&self) where T: Tr ensures self.dv() == 5;
}
impl Tr for A { }
impl V<A> for B { proof fn lv(&self) { } }
impl V<B> for B { proof fn lv(&self) { } }
} // verus!
