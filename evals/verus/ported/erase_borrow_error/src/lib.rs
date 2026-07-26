pub fn test_regression_70() {
    let v = 6u64;
    m(&mut v);
}

fn m(_v: &mut u64) {}
