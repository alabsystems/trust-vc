::verus_builtin_macros::verus!{
trait T {
    spec fn val(&self) -> u8;
    fn get(&self) -> (r: u8)
        ensures r == self.val();
}
impl T for u8 {
    spec fn val(&self) -> u8 { *self }
    fn get(&self) -> (r: u8) { *self }
}
fn test(x: u8) {
    let y = x.get();
    assert(y == 0);
}
}
