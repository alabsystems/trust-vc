::verus_builtin_macros::verus!{
fn id(v: u64) -> (ret: u64)
    ensures v == ret
{
    v
}

fn test1() {
    let mut a = 12;
    let b = id({
        a = a + 1;
        a
    });
    assert(b == 13);
}
}
