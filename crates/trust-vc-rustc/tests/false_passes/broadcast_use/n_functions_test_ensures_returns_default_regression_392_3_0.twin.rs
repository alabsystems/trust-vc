::verus_builtin_macros::verus!{
spec fn foo() -> bool { true }

fn returns_unit() ensures foo() { }

fn takes_unit(u: ()) { }

fn test(b: bool) { reveal(foo);
    takes_unit(returns_unit());
}
}
