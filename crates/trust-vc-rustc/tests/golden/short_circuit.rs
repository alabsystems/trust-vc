// Short-circuit operators whose right side assigns become `if` statements
// over a temporary; pure ones stay expressions.
verus! {

fn f(a: bool, b: bool) {
    let mut x: u64 = 0;
    let y = a && b;
    let z = a || { x = x + 1; b };
    assert(y ==> z);
}

proof fn g(a: bool, b: bool) {
    let mut x: u64 = 0;
    let z: bool = imply(a, { x = add(x, 1); b });
    assert(z || !a);
}

} // verus!
