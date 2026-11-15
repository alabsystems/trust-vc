// An exec assignment to an immutable local is left to rustc, but a mode
// error later in the same function comes first, as Verus checks modes before
// lifetimes.
verus! {

proof fn lemma() {
}

fn test() {
    let x: u64 = 1;
    x = 2;
    lemma();
}

} // verus!
