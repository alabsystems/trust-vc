::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
#[verifier::external_body]
fn mke_() {
} macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
struct Foo { b: u64, a: u64 }

fn test_fails() {
    let mut x = 24;
    let mut y = 30;

    let z = Foo { a: x, b: ({ x = 60; y }) };

    assert(z === Foo { a: 60, b: 30 }); // FAILS
}

fn test_ok() { mk_!();
    let mut x = 24;
    let mut y = 30;

    let z = Foo { a: x, b: ({ x = 60; y }) };

    assert(z === Foo { a: 24, b: 30 });
    assert(x == 60);
}

fn test2_fails() {
    let mut x = 24;
    let mut y = 30;

    let z = Foo { a: ({ x = 60; y }), b: x };

    assert(z === Foo { a: 30, b: 24 }); // FAILS
}

fn test2_ok() {
    let mut x = 24;
    let mut y = 30;

    let z = Foo { a: ({ x = 60; y }), b: x };

    assert(z === Foo { a: 30, b: 60 });
    assert(x == 60);
}
}
