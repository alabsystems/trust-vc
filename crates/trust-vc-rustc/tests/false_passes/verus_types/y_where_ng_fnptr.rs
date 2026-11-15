::verus_builtin_macros::verus!{
pub trait Tr { }
fn f() where fn(): Sized { }
fn user() { f(); }
}
