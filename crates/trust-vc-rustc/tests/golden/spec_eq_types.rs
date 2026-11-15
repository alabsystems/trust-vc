// Verus's type rule for spec `==`: the reader reports Verus's error, with
// Verus's type spelling, before it needs to represent the types.
verus! {

fn test(a: u64, b: Option<u64>)
    requires
        a == b,
{
}

} // verus!
