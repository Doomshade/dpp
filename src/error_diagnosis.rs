use std::error::Error;
use std::fmt::{Debug, Display, Formatter};

pub struct SyntaxError {
    error_messages: Vec<String>,
}

impl Debug for SyntaxError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Syntax error")?;
        for error_message in &self.error_messages {
            writeln!(f, "{}", error_message)?;
        }
        Ok(())
    }
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Syntax error")
    }
}

impl Error for SyntaxError {}

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
        let message = ErrorMessage {
            row,
            col,
            message: String::from(error),
        };
        self.error_messages.push(message);
    }

    pub fn check_errors(&self) -> Result<(), SyntaxError> {
        let error_messages = &self.error_messages;
        if error_messages.is_empty() {
            return Ok(());
        }
        let mut errors = Vec::new();

        for error_message in error_messages {
            errors.push(format!(
                "{}:{}:{}: {}",
                self.file_name, error_message.row, error_message.col, error_message.message
            ));
        }
        Err(SyntaxError {
            error_messages: errors,
        })
    }
}
