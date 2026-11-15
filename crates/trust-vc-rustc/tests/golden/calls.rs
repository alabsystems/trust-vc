// Calls: an exec call whose value is used, one whose value is discarded,
// and proof calls inside a proof block.
verus! {

fn double(x: u32) -> (r: u32)
    requires
        x < 1000,
    ensures
        r == 2 * x,
{
    x + x
}

proof fn lemma(a: int, b: int)
    requires
        a <= b,
    ensures
        a + 1 <= b + 1,
{
}

fn caller(a: int) {
    let d = double(3);
    let _ = double(4);
    proof {
        lemma(a, a + 1);
    }
    assert(d == 6);
}

} // verus!
