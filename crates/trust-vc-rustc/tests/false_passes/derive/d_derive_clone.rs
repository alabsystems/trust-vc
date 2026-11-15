::verus_builtin_macros::verus!{
#[derive(Clone)]
pub struct NC { pub v: u8 }
fn user(x: NC) -> NC { x }
}
