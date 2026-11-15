::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
struct Q { v: u8 }
impl Q { uninterp spec fn u(&self) -> bool; }
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) { consume(s); }
}
