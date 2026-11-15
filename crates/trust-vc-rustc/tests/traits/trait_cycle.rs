::verus_builtin_macros::verus!{
spec fn g<A: T1>(a: &A) -> bool {
    true
}
struct S1 {}
trait T1 {
    fn r(&self) -> bool;
}
impl T1 for S1 {
    fn r(&self) -> bool {
        true
    }
}
}
