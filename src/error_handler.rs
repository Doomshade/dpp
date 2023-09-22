struct ErrorHandler {
    file_name: String,
}

impl ErrorHandler {
    pub fn new(file_name: &str) -> Self {
        Self {
            file_name: String::from(file_name),
        }
    }

    pub fn handle(&self, row: u32, col: u32, error: &str) {
        println!(
            "Error in file {}:{}:{} - {}",
            self.file_name, row, col, error
        );
    }
}
