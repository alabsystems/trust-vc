::verus_builtin_macros::verus!{
struct X {
    i: u8,
    j: u8,
}

struct Y {
    x: X,
}

fn get_i() -> (res: u8) ensures res == 10 { 10 }

fn tup_test1() {
    let mut y = (Y { x: X { i: 12, j: 25 } }, 13);
    #[verifier::proof_note("m")] y.0.x.i = 10;
}
}
