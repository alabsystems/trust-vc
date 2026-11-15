pub trait Sub: Q + Tr { }
pub use self::Q as Sub2;
verus!{
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
pub struct S<X> { pub x: X }
pub fn f0<X: Sub2>(s: Z) -> (r: u8) ensures r != <Z as U<X>>::mm(&s) { 2 }
} // verus!
