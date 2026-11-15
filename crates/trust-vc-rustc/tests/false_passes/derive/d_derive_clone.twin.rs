::verus_builtin_macros::verus!{
#[derive(Hash)]
pub struct NC { pub v: u8 }
fn user(x: NC) -> NC { x }
}
