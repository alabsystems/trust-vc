// Expressions of type `!` in value position are lowered as statements, with
// an uninitialized temporary standing in for the value they never produce.
verus! {

fn early(b: bool) -> (i: u64)
    ensures
        10 <= i,
{
    if b {
        return 20;
    }
    30
}

fn both(b: bool) -> (i: u64) {
    if b {
        return 1;
    } else {
        return 2;
    }
}

fn foo(x: u64) {
}

fn as_argument() {
    foo({ return; });
}

fn in_let() -> u32 {
    let y: u32 = { return 2; };
    y
}

#[verifier::exec_allows_no_decreases_clause]
fn endless() {
    loop {}
}

} // verus!
