::verus_builtin_macros::verus!{
pub struct R<'a> { pub a: u8, pub r: &'a R<'a> }
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<R<'static>>(1); }
fn user() { assert(1 + 1 == 2); }
}
