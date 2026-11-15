::verus_builtin_macros::verus!{
trait T {
    proof fn f(&self);
}
struct S {}
impl T for S {
    proof fn f(&self) {
        assert(true);
    }
}
}
