pub trait HelloMacro {
    fn hello_macro();
}

pub trait Pos {
    #[must_use]
    fn position(&self) -> (u32, u32);
}
