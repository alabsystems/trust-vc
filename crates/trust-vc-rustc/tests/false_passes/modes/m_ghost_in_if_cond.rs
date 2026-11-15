::verus_builtin_macros::verus!{
fn g() -> u64 {
    let ghost a: bool = true;
    if a { 1 } else { 2 }
}
}
