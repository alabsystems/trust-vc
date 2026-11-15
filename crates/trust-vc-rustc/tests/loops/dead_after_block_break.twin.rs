verus! {
fn t() {
    let mut x: u64 = 0;
    loop
        decreases 1int,
    {
        { break; }
        x = 1;
    }
    assert(x == 0);
}
}
