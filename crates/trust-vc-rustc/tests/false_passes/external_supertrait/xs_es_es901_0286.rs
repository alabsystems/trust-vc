pub trait Sub: Tr { }
verus!{
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait U<T> {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
impl<T: Tr> U<T> for Z {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub fn f0<X: Sub>(s: Z) -> (r: u8) ensures r == <Z as U<X>>::mm(&s) { 2 }
} // verus!
