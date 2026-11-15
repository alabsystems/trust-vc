::verus_builtin_macros::verus!{
mod m { pub uninterp spec fn u() -> bool; }
fn f() { let x: u8; x = 5; x = 7; }
}
