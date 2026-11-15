pub use self::Tr as Sub;
verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub proof fn f<X>(s: S<X>) where S<X>: Sub ensures s.mm() == 2 { }
} // verus!
