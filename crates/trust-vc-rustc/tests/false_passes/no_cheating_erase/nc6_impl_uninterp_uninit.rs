::verus_builtin_macros::verus!{
struct Q { v: u8 }
impl Q { uninterp spec fn u(&self) -> bool; }
fn f() -> u8 { let x: u8; x }
}
