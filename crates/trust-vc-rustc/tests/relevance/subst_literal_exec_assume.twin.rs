verus! {
spec fn s(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + s(n - 1) }
}
fn t(b: bool, c: bool, xe: u64) {
    let ghost x: int = xe as int;
    proof {
        assume((if b { c } else { !b }));
        assume(s(if b { 1int } else { x }) == s(1));
    }
    proof { assert(s(0) == 0); }
    proof { assert(s(2) == 3); }
}
}
