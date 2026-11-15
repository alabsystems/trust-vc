::verus_builtin_macros::verus!{
pub trait T {
    #[verifier::loop_isolation(false)]
    proof fn f(&self) ensures false;
}
proof fn user<A: T>(a: &A) ensures false { a.f(); }
}
