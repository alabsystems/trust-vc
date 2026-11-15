verus! {
proof fn dec(i: nat, j: nat) {
    assert(decreases_to!(i + 1 => i));
    let tmp = decreases_to!(i, j + 1 => i, j);
    assert(tmp);
}
}
