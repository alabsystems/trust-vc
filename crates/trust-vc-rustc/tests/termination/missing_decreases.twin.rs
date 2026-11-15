verus! {
proof fn count_down(i: nat)
    decreases i {
    if i != 0 {
        count_down((i - 1) as nat);
    }
}
}
