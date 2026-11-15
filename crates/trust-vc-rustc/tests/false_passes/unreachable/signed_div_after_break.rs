verus! {
fn t() {
    let mut x: i64 = 4;
    loop
        decreases 1int,
    {
        break;
        x = x / 2;
    }
}
}
