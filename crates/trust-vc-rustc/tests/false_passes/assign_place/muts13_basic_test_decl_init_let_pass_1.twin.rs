::verus_builtin_macros::verus!{
fn test1() {
    let x: u64;
    #[allow(unused_assignments)]
    x = 23;
}
}
