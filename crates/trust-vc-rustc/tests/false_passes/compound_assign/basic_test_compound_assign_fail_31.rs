::verus_builtin_macros::verus!{
fn test1(x: &mut u32, y: u32) {
    *x /= y; // FAILS
}

fn test2(x: i8) {
    let mut x = x;
    x += { x = 1; 1 };// FAILS
}

fn test3a() {
    let mut x: u8 = 200;
    x = x + 100u8; // FAILS
    assert(x < 256);
}

fn test3b() {
    let mut x: u8 = 200;
    x += 100u8; // FAILS
    assert(x < 256);
}
}
