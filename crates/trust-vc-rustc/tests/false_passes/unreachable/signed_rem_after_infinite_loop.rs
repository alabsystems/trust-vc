verus! {
#[verifier::exec_allows_no_decreases_clause]
fn t(a: i32) {
    loop {}
    let z: i32 = a % 3;
}
}
