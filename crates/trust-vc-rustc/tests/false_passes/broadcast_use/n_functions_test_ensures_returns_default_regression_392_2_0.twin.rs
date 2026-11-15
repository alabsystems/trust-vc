::verus_builtin_macros::verus!{
spec fn foo() -> bool { true }

fn returns_unit() ensures foo() { }

fn test(b: bool) { reveal(foo);
    let x: ();
    if b {
        x = returns_unit();
    }
}
}
