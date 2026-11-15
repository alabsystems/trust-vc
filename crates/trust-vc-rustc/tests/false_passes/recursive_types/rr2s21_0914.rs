::verus_builtin_macros::verus!{
pub struct S0(pub nat, pub (), pub &'static S0);
pub trait Tr2 { }
impl Tr2 for S0 { }
proof fn user() { }
}
