// A trait with only unbounded associated types cannot produce a Verus error
// while VIR is built, so a first-phase Verus error elsewhere rejects the
// crate; a trait with a bound is refused outright.
verus! {

trait A {
    type AT;
}

fn test(a: u64, b: Option<u64>)
    requires
        a == b,
{
}

} // verus!
