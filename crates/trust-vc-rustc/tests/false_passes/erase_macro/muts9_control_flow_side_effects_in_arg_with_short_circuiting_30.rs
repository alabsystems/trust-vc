fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
fn test_fails() {
    let mut x = true;
    let mut y = true;

    let z = x && ({ x = false; y });

    assert(z == false); // FAILS
}

fn test_ok() {
    let mut x = true;
    let mut y = true;

    let z = x && ({ x = false; y });

    assert(z == true);
    assert(x == false);
}

fn test2_fails() {
    let mut x = true;
    let mut y = true;

    let z = ({ x = false; y }) && x;

    assert(z == true); // FAILS
}

fn test2_ok() { crate::mk_!();
    let mut x = true;
    let mut y = true;

    let z = ({ x = false; y }) && x;

    assert(z == false);
    assert(x == false);
}

fn test3_fails() {
    let mut x = true;
    let mut y = true;
    let mut w = false;

    let z = ({ x = false; y }) && ({ w = true; x });

    assert(z == true); // FAILS
}

fn test3_ok() {
    let mut x = true;
    let mut y = true;
    let mut w = false;

    let z = ({ x = false; y }) && ({ w = true; x });

    assert(w == true);
    assert(x == false);
    assert(z == false);
}
}
