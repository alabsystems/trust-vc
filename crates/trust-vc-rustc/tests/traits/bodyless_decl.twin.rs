::verus_builtin_macros::verus!{
trait Marshalable {
    open spec fn is_marshalable(&self) -> bool;
    exec fn _is_marshalable(&self) -> (res: bool)
        ensures res == self.is_marshalable(),
    ;
}
}
