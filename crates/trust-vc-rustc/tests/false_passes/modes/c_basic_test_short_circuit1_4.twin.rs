::verus_builtin_macros::verus!{
proof fn f3(a: bool, b: bool) {
    let mut x: u64 = 0;
    let y: bool = imply(a, b);
    let z: bool = imply(a, { x = add(x, 1); b });
    assert(y == z);
    assert((x == 1) == a);
}
}
