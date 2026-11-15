::verus_builtin_macros::verus!{
trait T {
    fn f(&self);
}
struct S {}
impl T for S {
    fn f(&self) requires true
    {
    }
}
}
