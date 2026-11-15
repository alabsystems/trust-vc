::verus_builtin_macros::verus!{
pub struct R<'a> { pub a: u8, pub r: &'a R<'a> }
spec fn sid<A>(a: int) -> int { a }
fn f() { assert(sid::<R<'static>>(1) == 1); }
fn user() { assert(1 + 1 == 2); }
}
