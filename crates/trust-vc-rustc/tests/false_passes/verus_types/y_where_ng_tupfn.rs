::verus_builtin_macros::verus!{
pub trait Tr { }
fn f() where (u8, fn(u8) -> u8): Sized { }
fn user() { f(); }
}
