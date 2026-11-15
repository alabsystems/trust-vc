pub use self::Q as SubQ;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait V {
    proof fn lv<X: SubQ>(&self, s: S<X>) ensures s.mm() == 2;
}
impl V for Z {
    proof fn lv<X: SubQ>(&self, s: S<X>) { }
}
} // verus!
