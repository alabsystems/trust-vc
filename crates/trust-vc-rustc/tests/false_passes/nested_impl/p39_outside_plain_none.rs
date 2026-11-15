::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
fn user(s: S) -> T { s.t }

}
fn plain() { impl Drop for S { fn drop(&mut self) {} } }
