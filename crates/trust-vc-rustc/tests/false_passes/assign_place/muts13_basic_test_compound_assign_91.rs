::verus_builtin_macros::verus!{
fn test1(y: &mut u32) {
    let mut x: i32 = 1;
    #[verifier::proof_note("m")] x += 2;
    assert({ x == 3 as i32 });
    *y /= 2;
    assert({ *y == *old(y)/2 });
}

proof fn test2a() {
    let mut x: u8 = 200;
    x = (x + 100u8) as u8;
    assert(x < 256);
}

proof fn test2b() {
    let mut x: u8 = 200;
    x += 100u8;
    assert(x < 256);
}

fn test3a() {
    let mut x: u8 = 200;
    x = x / (x + 1);
    assert(x < 256);
}

fn test3b() {
    let mut x: u8 = 200;
    x /= (x + 1);
    assert(x < 256);
}
}
