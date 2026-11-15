::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
fn test1() {
    let x: u64;
    #[allow(unused_assignments)]
    x = 23;
    x = 23;
}
}
