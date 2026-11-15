// Spec functions: a let chain, an opaque function, an uninterpreted one, and
// reveal/hide statements in exec code.
verus! {

spec fn f1(i: int, j: int) -> bool {
    i <= j
}

spec fn f2(i: int, j: int) -> bool {
    let x = i;
    let y = j;
    x < y
}

#[verifier::opaque]
spec fn f3(i: int, j: int) -> bool {
    f1(j, i)
}

uninterp spec fn g(i: int) -> bool;

fn uses(a: int, b: int) {
    hide(f2);
    assume(f2(a, b));
    proof {
        reveal(f2);
    }
    assert(f1(a, b));
    proof {
        reveal_with_fuel(f3, 3);
    }
    assert(g(a) ==> g(a));
}

} // verus!
