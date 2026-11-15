::verus_builtin_macros::verus!{
pub struct R<'a> { pub a: u8, pub r: &'a R<'a> }
proof fn pid<A>() { }
proof fn p() { pid::<&'static R<'static>>(); }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
