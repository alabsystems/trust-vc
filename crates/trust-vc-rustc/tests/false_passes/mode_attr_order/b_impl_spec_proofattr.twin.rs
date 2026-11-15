::verus_builtin_macros::verus!{
pub trait T {
    spec fn s(&self) -> bool;
}
pub struct S;
impl T for S {
    #[verifier::spec]
    open spec fn s(&self) -> bool { true }
}
fn user() { }
}
