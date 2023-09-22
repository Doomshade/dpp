use std::fmt::Error;

#[derive(Debug)]
struct ErrorMessage {
    row: u32,
    col: u32,
    message: String,
}

#[derive(Debug)]
pub struct ErrorDiagnosis {
    file_name: String,
    error_messages: Vec<ErrorMessage>,
}

impl ErrorDiagnosis {
    pub fn new(file_name: &str) -> Self {
        Self {
            file_name: String::from(file_name),
            error_messages: Vec::new(),
        }
    }

    pub fn handle(&mut self, error: &str) {
        self.handle_error_at(0, 0, error)
    }

    pub fn handle_error_at(&mut self, row: u32, col: u32, error: &str) {
        self.error_messages.push(ErrorMessage {
            row,
            col,
            message: String::from(error),
        });
    }

    pub fn check_errors(&self) -> Result<(), Error> {
        if self.error_messages.is_empty() {
            return Ok(());
        }

        for error_message in &self.error_messages {
            println!(
                "{}:{}:{}: error: {}",
                self.file_name, error_message.row, error_message.col, error_message.message
            );
        }
        Err(Error)
    }
}
