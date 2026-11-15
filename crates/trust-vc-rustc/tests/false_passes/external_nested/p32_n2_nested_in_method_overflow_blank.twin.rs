::verus_builtin_macros::verus!{
pub struct T { pub x: u8 }
impl T {
    // no attribute
    fn e(&self) { fn inner(x: u8) -> u8 { x + 1 } }
}
fn f() {}
}
