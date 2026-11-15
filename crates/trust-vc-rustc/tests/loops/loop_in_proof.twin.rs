verus! {
fn p() {
    let mut i: u32 = 0;
    while i < 10 invariant i <= 10 decreases 10 - i { i = (i + 1) as u32; }
}
}
