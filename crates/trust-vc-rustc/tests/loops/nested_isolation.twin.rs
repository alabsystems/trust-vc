verus! {
fn f() {
    let mut i: u32 = 0;
    let mut j: u32 = 0;
    while i < 10
        invariant i <= 10, j <= 5
        decreases 10 - i
    {
        i = i + 1;
        j = 0;
        while j < 5
            invariant j <= 5
            decreases 5 - j
        {
            assert(i <= 10);
            j = j + 1;
        }
    }
    assert(i == 10);
}
}
