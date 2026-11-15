verus! {
fn test(b: bool) {
    let mut c = b;
    while c
        decreases if c { 1int } else { 0int }
    {
        c = false;
        break;
    }
    assert(!c);
}
}
