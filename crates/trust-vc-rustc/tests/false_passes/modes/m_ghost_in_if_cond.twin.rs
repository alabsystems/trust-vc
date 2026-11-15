::verus_builtin_macros::verus!{
fn g() -> u64 {
    let ghost a: bool = true;
    if true { 1 } else { 2 }
}
}
