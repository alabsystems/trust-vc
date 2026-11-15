macro_rules! mkdrop { () => { impl Drop for S { fn drop(&mut self) {} } } }
::verus_builtin_macros::verus!{
pub struct T { pub y: u8 }
pub struct S { pub t: T }
type A = [u8; { 1 }];
fn user(s: S) -> T { s.t }
}
