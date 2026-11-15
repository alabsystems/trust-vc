pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
impl<T: Q> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub fn f0<X: Sub2>(s: Z) -> (r: u8) ensures r == <Z as U<X>>::mm(&s) { 2 }
} // verus!
