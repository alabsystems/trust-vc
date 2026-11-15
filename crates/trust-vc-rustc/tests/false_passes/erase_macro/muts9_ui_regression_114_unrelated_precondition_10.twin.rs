fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
fn get_bool() -> (b: bool)
    ensures b == true
{
    true
}

fn require_false() -> bool
    requires false // INCORRECT CONTEXT
{ crate::mk_!();
    false
}

fn test() {
    let x = 6;

    if !get_bool() {
        require_false();
    }

    assert(x == 7); // FAILS
}
}
