verus! {
fn f() {
    let mut i: u8 = 0;
    while i + 1 < 100
        invariant i <= 255
        decreases 100 - i
    {
        i = i + 1;
    }
}
}
