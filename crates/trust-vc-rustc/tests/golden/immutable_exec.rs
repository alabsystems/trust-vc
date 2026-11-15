// An exec assignment to an immutable variable is rustc's error (E0384), from
// the erase run; the reader leaves it to rustc.
verus! {

fn test() {
    let x: u64 = 10;
    x = 20;
}

} // verus!
