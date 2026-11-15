::verus_builtin_macros::verus!{
pub struct R { pub a: u8, pub b: &'static B1 }
pub struct B1 { pub a: u8, pub c: &'static R }
proof fn pid<A>() { }
proof fn p() { pid::<&'static R>(); }
fn f() {}
fn user() { assert(1 + 1 == 2); }
}
