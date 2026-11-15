::verus_builtin_macros::verus!{
mod m1 {
    pub trait SomeTrait {
        spec fn foo(&self) -> bool;
    }
    pub struct SomeType { pub b: bool }
    impl SomeTrait for SomeType {
        spec fn foo(&self) -> bool { self.b }
    }
}
}
