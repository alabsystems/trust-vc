verus!{
pub trait Tr {
    spec fn v(&self) -> int;
    fn get(&self) -> (r: u8) ensures r as int == self.v();
}
impl Tr for u8 {
    open spec fn v(&self) -> int { *self as int }
    fn get(&self) -> (r: u8) { *self }
}
pub struct W<X> { pub w: X }
impl<X: Tr> Tr for W<X> {
    open spec fn v(&self) -> int { self.w.v() }
    fn get(&self) -> (r: u8) { self.w.get() }
}
fn gv<T: Tr>(t: &T) -> (r: u8) ensures r as int == t.v() { t.get() }
fn user1() { let w = W { w: 6u8 }; let r = gv(&w); assert(r == 7); }
}
