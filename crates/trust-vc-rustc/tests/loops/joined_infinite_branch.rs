verus! {
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn t(b: bool) {
    let x = if b {
        1
    } else {
        while true { }
        5
    };
    assert(x == 1);
}
}
