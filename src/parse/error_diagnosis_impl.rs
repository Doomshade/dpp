use crate::parse::analysis::BoundDataType;
use crate::parse::error_diagnosis::{ErrorMessage, SyntaxError};
use crate::parse::ErrorDiagnosis;
use dpp_macros::Pos;
use itertools::Itertools;
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

    pub fn identifiers_cannot_have_nonascii(&mut self, position: (u32, u32), identifier: &str) {
        self.insert_error_message(
            position,
            format!(
                "Identifiers cannot have non-ascii characters: \"{identifier}\"",
                identifier = identifier
            )
            .as_str(),
        );
    }

    pub fn invalid_return_type(
        &mut self,
        position: (u32, u32),
        identifier: &str,
        expected_return_type: &DataType,
        got_return_type: &DataType,
    ) {
        self.insert_error_message(
            position,
            format!(
                "Invalid return type for function \"{identifier}\". Expected {expected_return_type}, got {got_return_type}.",
                identifier = identifier,
                expected_return_type = expected_return_type,
                got_return_type = got_return_type
            )
            .as_str(),
        );
    }

    pub fn unknown_operator(&mut self, position: (u32, u32), operator: &str) {
        self.insert_error_message(
            position,
            format!("Unknown operator \"{operator}\"").as_str(),
        );
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

    pub fn invalid_continue_placement(&mut self, position: (u32, u32)) {
        self.insert_error_message(position, "Invalid continue placement.");
    }

    pub fn invalid_token(&mut self, token: &Token<'a>) {
        self.insert_error_message(token.position(), format!("Invalid token {token}.").as_str());
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
            format!("Function with name \"{function_name}\" already exists.").as_str(),
        );
    }

    pub fn struct_already_exists(&mut self, position: (u32, u32), struct_name: &'a str) {
        self.insert_error_message(
            position,
            format!("Struct with name \"{struct_name}\" already exists.").as_str(),
        );
    }

    pub fn invalid_number(&mut self, position: (u32, u32)) {
        self.insert_error_message(position, "Invalid number.");
    }

    pub fn no_main_method_found_error(&mut self) {
        self.insert_error_message((0, 0), "No main method found.");
    }

    pub fn function_does_not_exist(&mut self, position: (u32, u32), identifier: &str) {
        self.insert_error_message(
            position,
            format!("Function \"{identifier}\" does not exist.").as_str(),
        );
    }
    pub fn struct_does_not_exist(&mut self, position: (u32, u32), identifier: &str) {
        self.insert_error_message(
            position,
            format!("Struct \"{identifier}\" does not exist.").as_str(),
        );
    }

    pub fn struct_declaration_invalid_field_amount(
        &mut self,
        position: (u32, u32),
        struct_identifier: &str,
        expected_size: usize,
        got_size: usize,
    ) {
        self.insert_error_message(
            position,
            format!(
                "Struct \"{struct_identifier}\" expects {expected_size} field(s), got {got_size}."
            )
            .as_str(),
        );
    }

    pub fn struct_field_not_found(
        &mut self,
        position: (u32, u32),
        struct_identifier: &str,
        field_identifier: &str,
    ) {
        self.insert_error_message(
            position,
            format!(
                "Struct field \"{field_identifier}\" does not exist for struct named \
            \"{struct_identifier}\"."
            )
            .as_str(),
        );
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

    pub fn invalid_main_function(&mut self, reason: &str) {
        self.insert_error_message(
            (0, 0),
            format!("Invalid main function. Reason: {reason}",).as_str(),
        );
    }

    pub fn unknown_data_type(&mut self, position: (u32, u32), reason: &str) {
        self.insert_error_message(position, format!("Unknown data type: {reason}").as_str());
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
            format!("Variable with name \"{var_name}\" already exists.").as_str(),
        );
    }
    pub fn cannot_assign_to_const_variable(&mut self, position: (u32, u32), var_name: &str) {
        self.insert_error_message(
            position,
            format!("Cannot assign to const variable \"{var_name}\".").as_str(),
        );
    }

    pub fn variable_not_found(&mut self, position: (u32, u32), var_name: &str) {
        self.insert_error_message(
            position,
            format!("Variable \"{var_name}\" does not exist.").as_str(),
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
        lhs: &BoundDataType,
        rhs: &BoundDataType,
    ) {
        self.insert_error_message(
            position,
            format!("Incompatible data types on lhs and rhs - {lhs} and {rhs}.").as_str(),
        );
    }

    pub fn invalid_data_type(
        &mut self,
        position: (u32, u32),
        expected_data_type: &BoundDataType,
        got: &BoundDataType,
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
            .collect_vec();

        Err(SyntaxError::new(vec))
    }
}
