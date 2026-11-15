// Fields marked `ghost` or `tracked` are refused, and so is a struct whose
// field has a refused struct type, whatever order they are declared in.
verus! {

struct Outer {
    inner: Inner,
    c: bool,
}

struct Inner {
    ghost a: nat,
    tracked b: i32,
}

fn test(o: Outer) -> bool {
    o.c
}

} // verus!
