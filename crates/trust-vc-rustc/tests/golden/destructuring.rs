// A destructuring assignment is a Verus error (unsupported feature).
verus! {

fn test() {
    let mut a = 0;
    let mut b = 0;
    (a, b) = (1, 2);
}

} // verus!
