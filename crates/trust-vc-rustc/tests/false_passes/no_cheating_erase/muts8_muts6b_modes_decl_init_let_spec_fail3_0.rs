::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
fn test1() {
    let x: u64;
    x = 2;
    x = 3;
    assert(!(false)); // FAILS
}
}
