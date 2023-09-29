use crate::parse::lexer::{Token, TokenKind};
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap};
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};

pub struct SyntaxError {
    error_messages: Vec<String>,
}

impl Debug for SyntaxError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Syntax error")?;
        for error_message in &self.error_messages {
            writeln!(f, "{error_message}")?;
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct ErrorMessage {
    row: u32,
    col: u32,
    message: String,
}

impl Ord for ErrorMessage {
    fn cmp(&self, other: &Self) -> Ordering {
        self.row
            .cmp(&other.row)
            .then_with(|| self.col.cmp(&other.col))
    }
}

impl PartialOrd for ErrorMessage {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
pub struct ErrorDiagnosis<'a> {
    file_name: String,
    file_contents: &'a str,
    /// Using hash map to remove duplicate messages
    error_messages: HashMap<String, ErrorMessage>,
}

impl<'a> ErrorDiagnosis<'a> {
    #[must_use]
    pub fn new(file_name: &str, file_contents: &'a str) -> Self {
        Self {
            file_name: String::from(file_name),
            file_contents,
            error_messages: HashMap::new(),
        }
    }

    pub fn handle(&mut self, error: &str) {
        self.handle_error_at(0, 0, error);
    }

    pub fn invalid_escaped_character(&mut self, row: u32, col: u32, character: char) {
        self.insert_error_message(row, col, format!("Invalid escaped character: {character}."));
    }

    pub fn unexpected_token_error(&mut self, token: &Token) {
        self.insert_error_message(token.row(), token.col(), format!("Unexpected {token}."));
    }

    pub fn expected_something_error(&mut self, error: &str, optional_token: Option<&Token>) {
        self.insert_error_message(
            optional_token.map_or(0, Token::row),
            optional_token.map_or(0, Token::col),
            format!("Expected {error}."),
        );
    }

    pub fn expected_different_token_error(
        &mut self,
        token: &Token,
        expected_token_kind: TokenKind,
    ) {
        self.insert_error_message(
            token.row(),
            token.col(),
            format!("Expected {expected_token_kind}."),
        );
    }

    pub fn handle_error_at(&mut self, row: u32, col: u32, error: &str) {
        self.insert_error_message(row, col, String::from(error));
    }

    pub fn variable_already_exists(&mut self, row: u32, col: u32, var_name: &str) {
        self.insert_error_message(row, col, format!("Variable \"{var_name}\" already exists."));
    }

    pub fn invalid_type(&mut self, row: u32, col: u32, var_name: &str) {
        self.insert_error_message(
            row,
            col,
            format!("Invalid type for variable \"{var_name}\"."),
        );
    }

    fn insert_error_message(&mut self, row: u32, col: u32, error: String) {
        let error_message = format!("{}:{}:{}: {}", self.file_name, row, col, error);
        if self.error_messages.contains_key(&error_message) {
            return;
        }
        let message_struct = ErrorMessage {
            row,
            col,
            message: error_message.clone(),
        };
        self.error_messages.insert(error_message, message_struct);
    }

    pub fn check_errors(&self) -> Result<(), SyntaxError> {
        let error_messages = &self.error_messages;
        if error_messages.is_empty() {
            return Ok(());
        }
        let mut priority_queue: BinaryHeap<ErrorMessage> = BinaryHeap::new();

        for (_, error_message) in error_messages {
            priority_queue.push(error_message.clone());
        }
        let vec = priority_queue
            .into_sorted_vec()
            .iter()
            .map(|x| x.message.clone())
            .collect();

        Err(SyntaxError {
            error_messages: vec,
        })
    }
}
