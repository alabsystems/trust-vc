::verus_builtin_macros::verus!{

pub struct E(pub u8);
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<E>(1); }
}
