::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
#[verifier::external_body]
fn mke_() {
} macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
fn example(x: u64, y: u64) -> (z: u64)
    ensures
        #![verifier::proof_note("Property 732")]
        z == x + y,
{
    x
}

fn caller() { mk_!();
    let _ = example(1, 2); // postcondition fails
}
}
