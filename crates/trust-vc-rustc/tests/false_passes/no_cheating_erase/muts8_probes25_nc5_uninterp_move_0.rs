::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
uninterp spec fn u() -> bool;
struct S { x: u8 }
fn consume(s: S) {}
fn f() {
    let s = S { x: 1 };
    consume(s);
    consume(s);
}

}
