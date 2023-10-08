pub struct ArenaAllocator {
    allocated_memory: &'static [u8; 125],
}

impl ArenaAllocator {
    pub fn new() -> Self {
        ArenaAllocator {
            allocated_memory: &[0u8; 125],
        }
    }
}
