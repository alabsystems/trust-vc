::verus_builtin_macros::verus!{
#[derive(PartialEq, Eq)]
pub struct G<T> { pub v: T }
fn user(x: G<u8>) -> (G<u8>, G<u8>) { (x, x) }
}
