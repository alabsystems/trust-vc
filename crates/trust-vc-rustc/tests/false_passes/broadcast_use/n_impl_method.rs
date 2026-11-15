::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn f() -> bool { true }
struct S { }
impl S { fn m(&self) { broadcast use f; assert(f()); } }
}
