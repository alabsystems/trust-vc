::verus_builtin_macros::verus!{
trait T {
    fn g(&self) -> (r: u8)
        ensures r < 10;
    fn h(&self) -> (r: u8)
        ensures r < 20
    {
        let x = self.g();
        x + 5
    }
}
}
