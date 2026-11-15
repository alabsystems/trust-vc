::verus_builtin_macros::verus!{
pub struct S<A> { pub a: A }
impl<A: Iterator> S<A> {
    fn get(&self) -> u8 { 1 }
}
fn f() { assert(1 + 1 == 2); }
}
