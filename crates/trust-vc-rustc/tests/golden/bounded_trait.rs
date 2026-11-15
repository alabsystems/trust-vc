// A trait whose associated type has a bound is refused even when a Verus
// error elsewhere would reject the crate.
verus! {

trait T {
    type A: T;
}

fn test(a: u64, b: Option<u64>)
    requires
        a == b,
{
}

} // verus!
