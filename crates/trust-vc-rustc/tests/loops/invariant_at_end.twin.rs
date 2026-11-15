verus! {
fn f() {
    let mut i: u32 = 0;
    loop
        invariant i < 10
        decreases 10 - i
    {
        if i == 10 {
            break;
        }
        i = i + 1;
    }
    assert(i <= 10);
}
}
