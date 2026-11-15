::verus_builtin_macros::verus!{
spec fn s(x: u64) -> u64 {
    let mut y = x;
    y = 1;
    y
}
}
