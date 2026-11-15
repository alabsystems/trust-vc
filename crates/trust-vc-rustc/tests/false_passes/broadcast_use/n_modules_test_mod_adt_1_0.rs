::verus_builtin_macros::verus!{
mod M1 {
    #[derive(PartialEq, Eq)]
    pub struct Car {
        pub four_doors: bool,
    }

    pub open spec fn is_four_doors(c: Car) -> bool {
        c.four_doors
    }
}
}
::verus_builtin_macros::verus!{
mod M2 {
    use crate::M1::{is_four_doors, Car};
    use verus_builtin::*;

    fn test() { broadcast use is_four_doors;
        let c = Car { four_doors: true };
        assert(is_four_doors(c));
    }
}
}
