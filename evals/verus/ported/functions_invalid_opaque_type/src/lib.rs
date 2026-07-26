trait FunctionsOpaqueFoo {
    fn bar(&self) -> bool;
}

type OT = impl FunctionsOpaqueFoo;
