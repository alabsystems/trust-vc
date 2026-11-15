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
pub proof fn f<X>(s: S<X>) where X: Sub { assert(s.mm() == 2); }
} // verus!
