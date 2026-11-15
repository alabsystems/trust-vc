// Places: a `&mut` parameter with `old`, struct construction, fields, and
// assignment to a field of a `mut` parameter.
verus! {

struct Pair {
    first: u32,
    second: bool,
}

spec fn second_of(p: Pair) -> bool {
    p.second
}

fn halve(y: &mut u32)
    ensures
        *y == *old(y) / 2,
{
    *y /= 2;
}

fn make() -> (p: Pair)
    ensures
        second_of(p),
{
    Pair { first: 7, second: true }
}

fn set_first(mut p: Pair) {
    p.first = 100;
    assert(p.first == 100);
}

} // verus!
