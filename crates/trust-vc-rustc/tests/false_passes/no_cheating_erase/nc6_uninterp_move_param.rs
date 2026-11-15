::verus_builtin_macros::verus!{
uninterp spec fn u() -> bool;
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) { consume(s); consume(s); }
}
