::verus_builtin_macros::verus!{
mod m { proof fn not_main() {} }
fn g() { assert(true); }
}
