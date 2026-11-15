// Exec arithmetic gets check sites; ghost arithmetic wraps into its type;
// clauses carry proof notes; spec arithmetic on machine integers is exact.
verus! {

fn sum(x: u64, y: u64) -> (z: u64)
    requires
        x < 100,
        #![verifier::proof_note("small y")]
        y < 100,
    ensures
        z == x + y,
{
    x + y
}

fn compound(a: u8, s: i16) {
    let mut b: u8 = a;
    b += 1;
    b = b / (b + 1);
    let c = -s;
    let d = a as u16;
}

proof fn ghost_arith(x: u8) {
    let mut y: u8 = x;
    y += 100u8;
    y = (y * 3) as u8;
    assert(y < 256);
}

} // verus!
