use crate::parse::error_diagnosis::{ErrorMessage, SyntaxError};
use crate::parse::ErrorDiagnosis;
use dpp_macros::Pos;
use std::collections::{BinaryHeap, HashMap};

use crate::parse::lexer::{Token, TokenKind};
use crate::parse::parser::DataType;

impl<'a, 'b> ErrorDiagnosis<'a, 'b> {
    #[must_use]
    pub fn new(file_name: &'b str, file_contents: &'a str) -> Self {
        Self {
            file_name,
            _file_contents: file_contents,
            error_messages: HashMap::new(),
        }
    }

    pub fn missing_return_statement(&mut self, position: (u32, u32)) {
        self.insert_error_message(position, "Missing return statement.");
    }

    pub fn invalid_escaped_character(&mut self, position: (u32, u32), character: char) {
        self.insert_error_message(
            position,
            format!("Invalid escaped character: {character}.").as_str(),
        );
    }

    pub fn invalid_break_placement(&mut self, position: (u32, u32)) {
        self.insert_error_message(position, "Invalid break placement.");
    }

    pub fn unexpected_token_error(&mut self, token: &Token<'a>) {
        self.insert_error_message(token.position(), format!("Unexpected {token}.").as_str());
    }

    pub fn not_implemented(&mut self, position: (u32, u32), error: &str) {
        self.insert_error_message(position, format!("Not yet implemented: {error}").as_str());
    }

    pub fn expected_something_error(&mut self, error: &str, optional_token: Option<&Token<'a>>) {
        self.insert_error_message(
            optional_token.map_or((0, 0), Token::position),
            format!("Expected {error}.").as_str(),
        );
    }

    pub fn function_already_exists(&mut self, position: (u32, u32), function_name: &'a str) {
        self.insert_error_message(
            position,
            format!("Function \"{function_name}\" already exists.").as_str(),
        );
    }

    pub fn invalid_number(&mut self, position: (u32, u32)) {
        self.insert_error_message(position, "Invalid number.");
    }

    pub fn no_main_method_found_error(&mut self) {
        self.insert_error_message((0, 0), "No main method found.");
    }

    pub fn function_does_not_exist(&mut self, position: (u32, u32)) {
        self.insert_error_message(position, "Function does not exist.");
    }

    pub fn invalid_number_of_arguments(
        &mut self,
        position: (u32, u32),
        identifier: &str,
        param_len: usize,
        arg_len: usize,
    ) {
        self.insert_error_message(
            position,
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
                token.position(),
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
        self.insert_error_message(token.position(), w.as_str());
    }

    pub fn expected_different_token_error(
        &mut self,
        token: &Token<'a>,
        expected_token_kind: TokenKind,
    ) {
        self.insert_error_message(
            token.position(),
            format!("Expected {expected_token_kind}.").as_str(),
        );
    }

    pub fn variable_already_exists(&mut self, position: (u32, u32), var_name: &str) {
        self.insert_error_message(
            position,
            format!("Variable \"{var_name}\" already exists.").as_str(),
        );
    }
    pub fn variable_not_found(&mut self, position: (u32, u32), var_name: &str) {
        self.insert_error_message(
            position,
            format!("Variable \"{var_name}\" was not found.").as_str(),
        );
    }

    pub fn variable_not_initialized(&mut self, position: (u32, u32), var_name: &str) {
        self.insert_error_message(
            position,
            format!("Variable \"{var_name}\" has not been initialized.").as_str(),
        );
    }

    pub fn mixed_data_types_error(
        &mut self,
        position: (u32, u32),
        lhs: &DataType<'a>,
        rhs: &DataType<'a>,
    ) {
        self.insert_error_message(
            position,
            format!("Mixed two data types - {lhs} and {rhs}.").as_str(),
        );
    }

    pub fn invalid_data_type(
        &mut self,
        position: (u32, u32),
        expected_data_type: &DataType<'a>,
        got: &DataType<'a>,
    ) {
        self.insert_error_message(
            position,
            format!("Invalid data type - expected {expected_data_type} got {got}.").as_str(),
        );
    }

    fn insert_error_message(&mut self, position: (u32, u32), error: &str) {
        let row = position.0;
        let col = position.1;
        let error_message;
        if row == 0 && col == 0 {
            error_message = format!("{}: {}", self.file_name, error);
        } else {
            error_message = format!("{}:{}:{}: {}", self.file_name, row, col, error);
        }
        if self.error_messages.contains_key(&error_message) {
            return;
        }

        let message_struct = ErrorMessage::new(row, col, error_message.clone());
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
            .map(|x| x.message().to_string())
            .collect();

        Err(SyntaxError::new(vec))
    }
}
