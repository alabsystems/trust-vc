// A closure bound to a name is not read, but Verus's spec `==` type rule
// still applies to it, with the closure type spelled as Verus spells it.
verus! {

fn test() {
    let a = |x: i32| x + 3;
    assert(a == 5);
}

fn same_closure() {
    let a = |x: i32| x + 3;
    assert(a == a);
}

} // verus!
