::verus_builtin_macros::verus!{
trait T {
    spec fn f(&self) -> bool;
}
struct S {}
impl T for S {
    spec fn f(&self) -> bool {
        true
    }
}
}
