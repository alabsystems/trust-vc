::verus_builtin_macros::verus!{
#[verifier::external]
pub trait Ex { }
pub struct S<T: Ex> { pub a: T }
fn f() { }
}
