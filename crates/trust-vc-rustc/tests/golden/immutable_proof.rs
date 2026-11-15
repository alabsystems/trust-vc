// In proof code the same assignment is Verus's error.
verus! {

proof fn test(x: u64) {
    x = 5;
}

} // verus!
