fn mke_() {
    #[macro_export]
    macro_rules! mk_ { () => { { let ms_ = crate::MutS_ { x: 1 }; let ma_ = ms_; } } }
}
::verus_builtin_macros::verus!{
pub struct MutS_ { pub x: u8 }
uninterp spec fn nc_u_() -> bool;
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

    fn test() { crate::mk_!();
        let c = Car { four_doors: true };
        assert(is_four_doors(c));
    }
}
}
