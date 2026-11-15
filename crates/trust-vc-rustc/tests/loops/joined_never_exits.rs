verus! {
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn t() -> (r: u64)
    ensures r == 7,
{
    let i: u64 = 0;
    while i < 10
        invariant i <= 10,
    {
    }
    3
}
}
