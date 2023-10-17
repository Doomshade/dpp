pub trait HelloMacro {
    fn hello_macro();
}

pub trait PosMacro {
    fn row(&self) -> u32;
    fn col(&self) -> u32;
}
