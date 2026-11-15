::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
#[verifier::external_body]
fn mke_() {
} macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
fn get_bool() -> (b: bool)
    ensures b == true
{ mk_!();
    true
}

fn require_false() -> bool
    requires false // INCORRECT CONTEXT
{
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
