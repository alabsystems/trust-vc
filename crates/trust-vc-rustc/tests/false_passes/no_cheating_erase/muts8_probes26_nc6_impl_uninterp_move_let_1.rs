::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
struct Q { v: u8 }
impl Q { uninterp spec fn u(&self) -> bool; }
struct S { x: u8 }
fn consume(s: S) {}
fn f() { let s = S { x: 1 }; let a = s; let b = s; }
}
