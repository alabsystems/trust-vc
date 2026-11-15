::verus_builtin_macros::verus!{
struct Foo {
    pub b: bool,
}

spec fn get_b(foo: Foo) -> bool {
    foo.b
}

fn test1() -> (b: Foo)
    ensures get_b(b)
{ broadcast use get_b;
    Foo { b: true }
}
}
