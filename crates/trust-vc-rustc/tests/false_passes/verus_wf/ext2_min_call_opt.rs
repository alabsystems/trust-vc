::verus_builtin_macros::verus!{
fn id<A>(a: u8) -> u8 { a }
fn f() { let x = id::<Option<u8>>(1); }
}
