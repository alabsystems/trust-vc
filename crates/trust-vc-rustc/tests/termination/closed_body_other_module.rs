verus! {
mod a {
    use verus_builtin::*;
    pub(crate) closed spec fn f(i: nat) -> nat
        decreases i
    {
        if i == 0 { 0 } else { 1 + f((i - 1) as nat) }
    }

    proof fn here() {
        assert(f(0) == 0);
    }
}
mod b {
    use verus_builtin::*;
    proof fn there() {
        assert(crate::a::f(0) == 0);
    }
}
}
