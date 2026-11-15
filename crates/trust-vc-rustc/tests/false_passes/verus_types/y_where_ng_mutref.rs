::verus_builtin_macros::verus!{
pub trait Tr { }
fn f() where &'static mut u8: Sized { }
fn user() { f(); }
}
