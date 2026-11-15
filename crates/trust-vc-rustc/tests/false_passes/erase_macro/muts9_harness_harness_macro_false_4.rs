::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
#[verifier::external_body]
fn mke_() {
} macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; let mb_ = ms_; } } }
fn empty() { mk_!(); }

fn harness2_macro() {
    assert(false); // FAILS
}
}
