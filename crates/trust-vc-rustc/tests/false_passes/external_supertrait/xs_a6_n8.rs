pub trait Sub: Q { }
verus!{
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub fn f<X: Sub>(s: S<X>) -> (r: u8) ensures r == 2 { proof { assert(s.mm() == 2); } 2 }
} // verus!
