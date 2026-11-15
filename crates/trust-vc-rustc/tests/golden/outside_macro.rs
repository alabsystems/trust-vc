// Items outside verus! that carry Verus attributes are refused (Verus would
// read them); verus! items inside an external module are external.
#[verifier::external_body]
fn outside(x: u64) -> u64 {
    x
}

#[verifier::external]
mod ext {
    use verus_builtin_macros::*;
    verus! {
    fn inside() {
        assert(false);
    }
    } // verus!
}

verus! {

#[verifier::external]
#[verifier::external_body]
fn both() {
}

} // verus!
