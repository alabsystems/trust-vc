::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
spec fn foo() -> bool { true }

fn returns_unit() ensures foo() { }

fn test(b: bool) {
    let x: ();
    if b {
        x = returns_unit();
        x = returns_unit();
    }
}
}
