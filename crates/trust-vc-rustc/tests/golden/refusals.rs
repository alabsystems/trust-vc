// Code outside the reader's fragment is refused with a tag, and the
// functions it could read are not reported as checked.
verus! {

fn uses_closure() {
    let f = |x: u32| x;
}

fn generic<const N: u64>(x: u64) -> u64 {
    x
}

trait Shape {
    type Unit;
    spec fn area(&self) -> int;
}

fn plain(x: u64) -> u64 {
    x
}

} // verus!
