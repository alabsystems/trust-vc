::verus_builtin_macros::verus!{
pub struct S {}
impl S { fn m<A>(x: u8) -> u8 { x } }
fn f() { let y = S::m::<[fn(); 2]>(1); }
}
