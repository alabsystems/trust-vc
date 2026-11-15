fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
fn foo(x: u64, y: u64) -> (ret: (u64, u64))
    ensures ret == (x, y)
{
    (x, y)
}

fn test_fails() {
    let mut x = 24;
    let mut y = 30;

    let z = foo(x, ({ x = 60; y }));

    assert(z === (60, 30)); // FAILS
}

fn test_ok() {
    let mut x = 24;
    let mut y = 30;

    let z = foo(x, ({ x = 60; y }));

    assert(z === (24, 30));
    assert(x == 60);
}

fn test2_fails() {
    let mut x = 24;
    let mut y = 30;

    let z = foo(({ x = 60; y }), x);

    assert(z === (30, 24)); // FAILS
}

fn test3_ok() { crate::mk_!();
    let mut x = 24;
    let mut y = 30;

    let z = foo(({ x = 60; x }), ({ x = 80; x }));

    assert(z === (60, 80));
}
}
