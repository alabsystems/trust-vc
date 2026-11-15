verus! {
fn t() {
    let mut x: u64 = 0;
    loop
        decreases 1int,
    {
        break;
        let y: u64 = 1;
    }
    assert(x == 0);
}
}
