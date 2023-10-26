pub trait HelloMacro {
    fn hello_macro();
}

pub trait Pos {
    #[must_use]
    fn row(&self) -> u32;
    #[must_use]
    fn col(&self) -> u32;
}
