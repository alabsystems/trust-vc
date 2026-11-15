// Operands are evaluated left to right: an assignment inside a later
// operand does not change the value an earlier operand already produced.
verus! {

fn left_first() {
    let mut x: u64 = 24;
    let y: u64 = 30;
    let z = x + ({ x = 60; y });
    assert(z == 54);
    assert(x == 60);
}

fn right_first() {
    let mut x: u64 = 24;
    let y: u64 = 30;
    let z = ({ x = 60; y }) + x;
    assert(z == 54); // fails: z is 90
}

} // verus!
