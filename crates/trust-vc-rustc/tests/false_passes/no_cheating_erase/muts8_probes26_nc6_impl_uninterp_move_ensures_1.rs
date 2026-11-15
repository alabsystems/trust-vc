::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
struct Q { v: u8 }
impl Q { uninterp spec fn u(&self) -> bool; }
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) -> (r: u8) ensures r == 1 { consume(s); consume(s); 1 }
}
