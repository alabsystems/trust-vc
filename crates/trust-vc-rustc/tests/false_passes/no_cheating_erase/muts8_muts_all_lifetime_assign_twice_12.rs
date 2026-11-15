::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
fn test() {
    let x: u8;
    x = 5;
    x = 7;

}
}
