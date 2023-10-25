use core::cmp::Ordering;
use core::fmt::{Debug, Display, Formatter};
use std::collections::{BinaryHeap, HashMap};
use std::error::Error;

use crate::parse::lexer::{Token, TokenKind};
use crate::parse::parser::DataType;

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
pub struct ErrorDiagnosis<'a, 'b> {
    file_name: &'b str,
    _file_contents: &'a str,
    /// Using hash map to remove duplicate messages
    error_messages: HashMap<String, ErrorMessage>,
}

impl<'a, 'b> ErrorDiagnosis<'a, 'b> {
    #[must_use]
    pub fn new(file_name: &'b str, file_contents: &'a str) -> Self {
        Self {
            file_name,
            _file_contents: file_contents,
            error_messages: HashMap::new(),
        }
    }

    pub fn missing_return_statement(&mut self, row: u32, col: u32) {
        self.insert_error_message(row, col, "Missing return statement.");
    }

    pub fn invalid_escaped_character(&mut self, row: u32, col: u32, character: char) {
        self.insert_error_message(
            row,
            col,
            format!("Invalid escaped character: {character}.").as_str(),
        );
    }

    pub fn invalid_break_placement(&mut self, row: u32, col: u32) {
        self.insert_error_message(row, col, "Invalid break placement.");
    }

    pub fn unexpected_token_error(&mut self, token: &Token<'a>) {
        self.insert_error_message(
            token.row(),
            token.col(),
            format!("Unexpected {token}.").as_str(),
        );
    }

    pub fn not_implemented(&mut self, error: &str) {
        self.insert_error_message(1, 1, format!("Not yet implemented: {error}").as_str());
    }

    pub fn expected_something_error(&mut self, error: &str, optional_token: Option<&Token<'a>>) {
        self.insert_error_message(
            optional_token.map_or(0, Token::row),
            optional_token.map_or(0, Token::col),
            format!("Expected {error}.").as_str(),
        );
    }

    pub fn function_already_exists(&mut self, row: u32, col: u32, function_name: &'a str) {
        self.insert_error_message(
            row,
            col,
            format!("Function \"{function_name}\" already exists.").as_str(),
        );
    }

    pub fn invalid_number(&mut self, row: u32, col: u32) {
        self.insert_error_message(row, col, "Invalid number.");
    }

    pub fn no_main_method_found_error(&mut self) {
        self.insert_error_message(0, 0, "No main method found.");
    }

    pub fn function_does_not_exist(&mut self, row: u32, col: u32) {
        self.insert_error_message(row, col, "Function does not exist.");
    }

    pub fn invalid_number_of_arguments(
        &mut self,
        row: u32,
        col: u32,
        identifier: &str,
        param_len: usize,
        arg_len: usize,
    ) {
        self.insert_error_message(
            row,
            col,
            format!(
                "Invalid number of arguments for function \"{}\". Expected {}, got {}.",
                identifier, param_len, arg_len
            )
            .as_str(),
        );
    }

    pub fn expected_one_of_token_error(
        &mut self,
        token: &Token<'a>,
        expected_one_of: &[TokenKind],
    ) {
        assert!(
            !expected_one_of.is_empty(),
            "Expected at least one token kind"
        );
        if expected_one_of.len() == 1 {
            self.insert_error_message(
                token.row(),
                token.col(),
                format!("Expected {}.", expected_one_of[0]).as_str(),
            );
            return;
        }
        let mut w = String::with_capacity(256);
        w.push_str("Expected one of: ");
        expected_one_of
            .iter()
            .for_each(|token_kind| w.push_str(format!("{token_kind}, ").as_str()));

        w.replace_range(w.len() - 2.., ".");
        self.insert_error_message(token.row(), token.col(), w.as_str());
    }

    pub fn expected_different_token_error(
        &mut self,
        token: &Token<'a>,
        expected_token_kind: TokenKind,
    ) {
        self.insert_error_message(
            token.row(),
            token.col(),
            format!("Expected {expected_token_kind}.").as_str(),
        );
    }

    pub fn variable_already_exists(&mut self, row: u32, col: u32, var_name: &str) {
        self.insert_error_message(
            row,
            col,
            format!("Variable \"{var_name}\" already exists.").as_str(),
        );
    }
    pub fn variable_not_found(&mut self, row: u32, col: u32, var_name: &str) {
        self.insert_error_message(
            row,
            col,
            format!("Variable \"{var_name}\" was not found.").as_str(),
        );
    }

    pub fn variable_not_initialized(&mut self, row: u32, col: u32, var_name: &str) {
        self.insert_error_message(
            row,
            col,
            format!("Variable \"{var_name}\" has not been initialized.").as_str(),
        );
    }

    pub fn mixed_data_types_error(
        &mut self,
        row: u32,
        col: u32,
        lhs: &DataType<'a>,
        rhs: &DataType<'a>,
    ) {
        self.insert_error_message(
            row,
            col,
            format!("Mixed two data types - {lhs} and {rhs}.").as_str(),
        );
    }

    pub fn invalid_data_type(
        &mut self,
        row: u32,
        col: u32,
        expected_data_type: &DataType<'a>,
        got: &DataType<'a>,
    ) {
        self.insert_error_message(
            row,
            col,
            format!("Invalid data type - expected {expected_data_type} got {got}.").as_str(),
        );
    }

    fn insert_error_message(&mut self, row: u32, col: u32, error: &str) {
        let error_message;
        if row == 0 && col == 0 {
            error_message = format!("{}: {}", self.file_name, error);
        } else {
            error_message = format!("{}:{}:{}: {}", self.file_name, row, col, error);
        }
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

        for error_message in error_messages.values() {
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
