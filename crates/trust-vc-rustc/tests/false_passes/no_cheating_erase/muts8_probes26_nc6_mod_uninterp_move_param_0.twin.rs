::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
mod m { pub uninterp spec fn u() -> bool; }
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) { consume(s); }
}
