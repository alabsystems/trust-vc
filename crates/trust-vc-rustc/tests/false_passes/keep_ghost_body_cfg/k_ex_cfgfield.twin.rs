::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
pub struct H { pub f: NC }
fn user(h: H) -> bool { let a = h.f; let b = h.f; true }
}
