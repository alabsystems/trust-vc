::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
#[verifier::external_body]
fn mke_() {
} macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
fn test_fails() {
    let mut x = 24;
    let mut y = 30;

    let z = x + ({ x = 60; y });

    assert(z == 90); // FAILS
}

fn test_ok() { mk_!();
    let mut x = 24;
    let mut y = 30;

    let z = x + ({ x = 60; y });

    assert(z == 54);
    assert(x == 60);
}

fn test2_fails() {
    let mut x = 24;
    let mut y = 30;

    let z = ({ x = 60; y }) + x;

    assert(z == 54); // FAILS
}

fn test2_ok() {
    let mut x = 24;
    let mut y = 30;

    let z = ({ x = 60; y }) + x;

    assert(z == 90);
    assert(x == 60);
}
}
