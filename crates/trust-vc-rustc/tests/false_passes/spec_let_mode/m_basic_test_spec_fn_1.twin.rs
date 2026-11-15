::verus_builtin_macros::verus!{
spec fn f1(i: int, j: int) -> bool {
    i <= j
}

spec fn f2(i: int, j: int) -> bool {
    let x = i;
    let ghost y = j;
    x < y
}

#[verifier(opaque)]
spec fn f3(i: int, j: int) -> bool {
    f1(j, i)
}

fn test_spec_fn(a: int, b: int) {
    hide(f2);

    assume(f2(a, b));
    proof {
        reveal(f2);
    }
    assert(f1(a, b));

    proof {
        reveal(f3);
    }
    assert(f3(b, a));
    assert(f3(a, b)); // FAILS
}
}
