::verus_builtin_macros::verus!{
spec fn s(x: u64) -> u64 {
    let mut y = x;
    let z: u64 = 1;
    y
}
}
