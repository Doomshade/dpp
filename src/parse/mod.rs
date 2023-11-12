use itertools::Itertools;
use std::io::Write;
use std::{cell, collections, fs, io, rc};

use dpp_macros::Pos;

use crate::parse::analysis::{
    BoundDataType, BoundLiteralValue, BoundTranslationUnit, BoundVariable, BoundVariablePosition,
    SymbolTable,
};
use crate::parse::emitter::{Address, DebugKeyword, Instruction, OperationType};
use crate::parse::error_diagnosis::ErrorMessage;
use crate::parse::lexer::{Token, TokenKind};
use crate::parse::parser::{Block, DataType, Expression, Function, Modifier, Variable};

pub mod analysis_impl;
pub mod emitter_impl;
pub mod error_diagnosis_impl;
pub mod lexer_impl;
pub mod optimizer_impl;
pub mod parser_impl;

#[derive(Debug)]
pub struct ErrorDiagnosis<'a, 'b> {
    file_name: &'b str,
    _file_contents: &'a str,
    /// Using hash map to remove duplicate messages
    error_messages: collections::HashMap<String, ErrorMessage>,
}

#[derive(Debug)]
pub struct Lexer<'a, 'b> {
    /// The raw translation unit input.
    raw_input: &'a str,
    /// The raw pointer to the string slice.
    pointer: usize,
    /// The input as a vector of characters because we want to index into it.
    chars: Vec<char>,
    /// The cursor to the chars vector.
    cursor: usize,
    /// The current row.
    row: u32,
    /// The current column.
    col: u32,
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
}

#[derive(Debug)]
pub struct Parser<'a, 'b> {
    /// An RC to the tokens. The RC is there just to ensure immutability -- we don't wanna mutate
    /// any token nor add any. TODO: This should probably be a peekable iterator.
    tokens: rc::Rc<Vec<Token<'a>>>,
    /// The current token index to the tokens vector. TODO: The tokens should be an iterator.
    curr_token_index: usize,
    /// The position of last token.
    position: (u32, u32),
    /// A flag that says whether we encountered an error. Used for error recovery.
    error: bool,
    /// A flag that says whether we are in the process of fixing the parsing process. Used for
    /// error recovery.
    fixing_parsing: bool,
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
}

#[derive(Debug)]
pub struct SemanticAnalyzer<'a, 'b> {
    /// The symbol table.
    symbol_table: SymbolTable<'a>,
    /// The current loop stack. Used to determine whether "break" or "continue" are out of place.
    loop_depth: usize,
    assignment_count: collections::HashMap<BoundVariable, usize>,
    referenced_variables: collections::HashSet<BoundVariable>,
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
}

#[derive(Debug)]
pub struct Optimizer {
    optimizations: Vec<String>,
    referenced_variables: collections::HashSet<BoundVariable>,
}

#[derive(Debug)]
pub struct Emitter<'a, 'b> {
    /// The instructions to be emitted.
    code: Vec<Instruction>,
    pc: usize,
    labels: collections::HashMap<String, usize>,
    /// The current control statement index.
    control_statement_count: u32,
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
}

impl<'a, 'b> Lexer<'a, 'b> {
    /// # Arguments
    ///
    /// * `input`: The translation unit input.
    /// * `error_diag`: The error diagnostics.
    ///
    /// returns: Lexer
    #[must_use]
    pub fn new(input: &'a str, error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>) -> Self {
        // Create a vector of characters from the input string. This is so that we can access the
        // characters by index. Unfortunately this will take up more memory, but as soon as the
        // lexer goes out of scope, the vector will be dropped.

        // NOTE: We would normally use an iterator here, but the problem is that we need to
        // be able to peek inside the iterator. The Peekable trait allows it, HOWEVER: the trait
        // consumes the iterator, which means that we can't use it anymore. So we have to use a
        // vector instead.
        let chars = input.chars().collect();
        Self {
            raw_input: input,
            chars,
            cursor: 0,
            pointer: 0,
            row: 1,
            col: 1,
            error_diag,
        }
    }

    fn position(&self) -> (u32, u32) {
        (self.row, self.col)
    }

    fn new_token(&self, kind: TokenKind, value: &'a str) -> Token<'a> {
        Token::new(kind, (self.row, self.col), value)
    }

    fn peek(&self) -> char {
        self.peek_ahead(0)
    }

    fn peek_ahead(&self, ahead: usize) -> char {
        if self.cursor + ahead >= self.chars.len() {
            return char::default();
        }

        self.chars[self.cursor + ahead]
    }

    #[must_use]
    fn advance(&mut self) -> usize {
        let advanced_bytes = self.peek().len_utf8();
        self.col += 1;
        self.cursor += 1;
        self.pointer += advanced_bytes;
        advanced_bytes
    }
}

impl<'a, 'b> Parser<'a, 'b> {
    pub fn new(
        tokens: rc::Rc<Vec<Token<'a>>>,
        error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
    ) -> Self {
        Self {
            position: (1, 1),
            tokens,
            curr_token_index: 0,
            error_diag,
            error: false,
            fixing_parsing: false,
        }
    }

    fn go_back(&mut self) {
        self.curr_token_index -= 1;
        if let Some(token) = self.token() {
            self.position = token.position();
        }
    }

    fn consume_token(&mut self) {
        self.curr_token_index += 1;
        if let Some(token) = self.token() {
            self.position = token.position();
        }
    }

    #[must_use]
    fn token(&self) -> Option<&Token<'a>> {
        return self.token_offset(0);
    }

    #[must_use]
    fn token_offset(&self, offset: i32) -> Option<&Token<'a>> {
        if self.curr_token_index as i32 + offset >= self.tokens.len() as i32
            || self.curr_token_index as i32 + offset < 0
        {
            return None;
        }
        Some(&self.tokens[(self.curr_token_index as i32 + offset) as usize])
    }

    fn matches_token_kind(&self, token_kind: TokenKind) -> bool {
        if let Some(token) = self.token() {
            return token.kind() == token_kind;
        }
        false
    }

    fn matches_one_from(&self, token_kinds: &[TokenKind]) -> Option<TokenKind> {
        if let Some(token) = self.token() {
            let token_kind = token.kind();
            return token_kinds
                .iter()
                .find(|arr_token| **arr_token == token_kind)
                .map(|x| token_kind);
        }
        None
    }

    fn expect_one_from(
        &mut self,
        expected_token_kinds: &[TokenKind],
    ) -> Option<(&'a str, TokenKind)> {
        if let Some(token) = self.token() {
            let token_kind = token.kind();
            let token_value = token.value();

            if expected_token_kinds
                .iter()
                .any(|expected_token_kind| expected_token_kind == &token_kind)
            {
                self.consume_token();
                self.error = false;
            } else {
                // Check if this is the second error in a row.
                // If it is, return None. This will signal that we should go into panic mode.
                // We let the callee handle this.
                if self.error {
                    return None;
                }

                // Log the error at the previous token as we expected something else there.
                if !self.fixing_parsing {
                    self.fixing_parsing = true;
                    if let Some(prev_token) = self.token_offset(-1) {
                        self.error_diag
                            .borrow_mut()
                            .expected_one_of_token_error(prev_token, expected_token_kinds);
                        self.consume_token();
                        let call_me_again = self.expect_one_from(expected_token_kinds);
                        self.fixing_parsing = false;
                        if let Some((a, b)) = call_me_again {
                            if self.error {
                                self.go_back();
                            } else {
                                return Some((a, b));
                            }
                        } else {
                            self.go_back();
                        }
                    } else {
                        unreachable!("No token found");
                    }
                }
                self.error = true;
            }

            return Some((token_value, token_kind));
        }
        None
    }

    fn matches_data_type(&self) -> bool {
        if let Some(token) = self.token() {
            return matches!(
                token.kind(),
                TokenKind::ABKeyword
                    | TokenKind::PpKeyword
                    | TokenKind::FlaccidKeyword
                    | TokenKind::PKeyword
                    | TokenKind::NoppKeyword
                    | TokenKind::BoobaKeyword
                    | TokenKind::YarnKeyword
            );
        }
        false
    }

    fn matches_modifier(&self) -> bool {
        if let Some(token) = self.token() {
            return matches!(token.kind(), TokenKind::ConstKeyword);
        }
        false
    }

    /// Expects a **token** of a certain kind. If the token is not present an error is added to the
    /// error diagnostics. If the token is present, it is consumed and the value of the token is
    /// returned. If the token has no value, an empty string is returned.
    ///
    /// Note that this function fabricates the token if it's not present to continue proper parsing.
    /// For example, if we expect a colon, but a semicolon is present, we add an error and continue
    /// as if a colon was present. This is useful for error recovery.
    ///
    /// If two expect check fails in a row we enter panic mode. This means that we start throwing
    /// out tokens until we find a synchronizing token and None is returned. Otherwise this function
    /// always returns Some even if an error, such as a missing token, is present.
    ///
    /// # Arguments
    ///
    /// * `token_kind`: The token kind to expect.
    ///
    /// returns: Some of the String value of the token. Is empty if it does not exist. None if the
    /// the parser enters panic mode.
    ///
    /// # Examples
    ///
    /// ```
    /// // Expect an open parenthesis. If it is not present, pretend it's
    /// // there and continue parsing.
    /// self.expect(TokenKind::OpenParen)?;
    ///
    /// // (...)
    ///
    /// // Expect a close parenthesis. If it is not present, pretend it's
    /// // there and continue parsing.
    /// self.expect(TokenKind::CloseParen)?;
    ///
    /// // or
    /// let identifier = self.expect(TokenKind::Identifier)?;
    ///
    /// ```
    fn expect(&mut self, expected_token_kind: TokenKind) -> Option<&'a str> {
        match self.expect_one_from(&[expected_token_kind]) {
            Some((value, _)) => Some(value),
            None => None,
        }
    }

    fn go_into_panic_mode(&mut self) {
        // Consume tokens until we find a synchronizing token.
        while let Some(token) = self.token() {
            match token.kind() {
                TokenKind::Eof
                | TokenKind::IfKeyword
                | TokenKind::ForKeyword
                | TokenKind::WhileKeyword
                | TokenKind::DoKeyword
                | TokenKind::LoopKeyword
                | TokenKind::BreakKeyword
                | TokenKind::ContinueKeyword
                | TokenKind::FUNcKeyword
                | TokenKind::SwitchKeyword
                | TokenKind::ByeKeyword
                | TokenKind::Semicolon => {
                    break;
                }
                _ => {
                    self.consume_token();
                    continue;
                }
            }
        }

        // Reset the error flag as we expect the next expect call to be valid.
        self.error = false;
    }

    fn add_error(&mut self, error_message: &str) {
        self.error_diag
            .borrow_mut()
            .expected_something_error(error_message, self.token_offset(-1));
    }

    // Wrappers for print! and println! macros to use
    // inside the Statement::PrintStatement.
    fn print(str: &str) {
        print!("{str}");
    }

    fn println(str: &str) {
        println!("{str}");
    }

    fn expect_token_separated<T>(
        &mut self,
        start_token_kind: TokenKind,
        end_token_kind: TokenKind,
        separator: TokenKind,
        consumer_function: fn(&mut Parser<'a, 'b>) -> Option<T>,
    ) -> Option<Vec<T>> {
        self.expect(start_token_kind)?;
        let mut vec = Vec::new();
        if self.matches_token_kind(end_token_kind) {
            self.expect(end_token_kind);
            return Some(vec);
        }

        vec.push(consumer_function(self)?);
        while !self.matches_token_kind(end_token_kind) && !self.matches_token_kind(TokenKind::Eof) {
            self.expect(separator)?;
            if self.matches_token_kind(end_token_kind) || self.matches_token_kind(TokenKind::Eof) {
                break;
            }
            vec.push(consumer_function(self)?);
        }
        self.expect(end_token_kind)?;
        Some(vec)
    }
}

impl<'a, 'b> SemanticAnalyzer<'a, 'b> {
    pub fn new(error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>) -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            error_diag,
            loop_depth: 0,
            assignment_count: collections::HashMap::new(),
            referenced_variables: collections::HashSet::new(),
        }
    }

    fn is_variable_in_scope(&self, ident: &'a str) -> bool {
        let maybe_variable = self.symbol_table().find_variable_declaration(ident);
        maybe_variable.0 == 0 && maybe_variable.1.is_some()
    }

    pub fn declare_variable(
        &mut self,
        position: (u32, u32),
        modifiers: Vec<Modifier>,
        data_type: BoundDataType,
        ident: &'a str,
        is_parameter: bool,
    ) {
        if self.is_variable_in_scope(ident) {
            self.error_diag
                .borrow_mut()
                .variable_already_exists(position, ident);
        }
        self.symbol_table_mut()
            .declare_variable(modifiers, data_type, ident, is_parameter)
    }

    fn symbol_table_mut(&mut self) -> &mut SymbolTable<'a> {
        &mut self.symbol_table
    }

    fn symbol_table(&self) -> &SymbolTable<'a> {
        &self.symbol_table
    }

    fn to_bound_data_type(&self, data_type: &DataType, position: (u32, u32)) -> BoundDataType {
        match BoundDataType::try_from((data_type, self.symbol_table())) {
            Ok(data_type) => data_type,
            Err(err) => {
                self.error_diag
                    .borrow_mut()
                    .unknown_data_type(position, &err.reason);
                err.dummy_data_type
            }
        }
    }

    fn to_bound_parameters(&self, parameters: &Vec<Variable<'a>>) -> Vec<BoundVariable> {
        let mut current_size = 0;
        parameters
            .iter()
            .map(|parameter| {
                let data_type =
                    self.to_bound_data_type(parameter.data_type(), parameter.position());
                let size = data_type.size();
                current_size += size;
                (
                    data_type,
                    -(current_size as i32),
                    parameter.has_modifier(Modifier::Const),
                )
            })
            .map(|(data_type, offset, is_const)| {
                BoundVariable::with_static_position(0, offset, data_type, is_const)
            })
            .collect_vec()
    }

    fn check_if_mixed_data_types(
        &self,
        expected_data_type: &BoundDataType,
        got: &BoundDataType,
        position: (u32, u32),
    ) {
        if expected_data_type != got {
            self.error_diag
                .borrow_mut()
                .mixed_data_types_error(position, expected_data_type, got)
        }
    }

    fn check_data_type(
        &self,
        expected_data_type: &BoundDataType,
        got: Option<&BoundDataType>,
        position: (u32, u32),
    ) {
        match got {
            Some(data_type) => {
                if expected_data_type != data_type {
                    self.error_diag.borrow_mut().invalid_data_type(
                        position,
                        expected_data_type,
                        data_type,
                    )
                }
            }
            None => {}
        }
    }

    fn begin_function(&mut self, function: &Function<'a>) {
        self.symbol_table_mut()
            .push_function_scope(function.identifier());
        function.parameters().iter().for_each(|parameter| {
            let data_type = self.to_bound_data_type(parameter.data_type(), parameter.position());
            self.declare_variable(
                parameter.position(),
                parameter.modifiers().clone(),
                data_type,
                parameter.identifier(),
                true,
            )
        });
    }

    fn end_function(&mut self) {
        self.symbol_table_mut().pop_scope();
    }
}

impl Optimizer {
    pub fn new() -> Self {
        Self {
            optimizations: Vec::new(),
            referenced_variables: collections::HashSet::new(),
        }
    }

    pub fn optimize(&mut self, translation_unit: BoundTranslationUnit) -> BoundTranslationUnit {
        self.optimize_translation_unit(translation_unit)
    }

    pub fn optimizations(&self) -> &Vec<String> {
        &self.optimizations
    }

    fn optimizations_mut(&mut self) -> &mut Vec<String> {
        &mut self.optimizations
    }
}

impl<'a, 'b> Emitter<'a, 'b> {
    pub fn new(error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>) -> Self {
        Self {
            error_diag,
            code: Vec::with_capacity(200),
            labels: collections::HashMap::new(),
            pc: 0,
            control_statement_count: 0,
        }
    }

    /// # Summary
    /// Generates instructions for the PL/0 interpreter.
    ///
    /// # Arguments
    /// * `translation_unit`: the translation unit
    ///
    /// # Returns
    /// * `Vec<Instruction>` - the instructions
    pub fn into_pl0_instructions(
        mut self,
        translation_unit: BoundTranslationUnit,
    ) -> Vec<Instruction> {
        self.emit_translation_unit(&translation_unit);

        self.code
    }

    /// # Summary
    /// Emits the translation unit to the writer.
    ///
    /// # Arguments
    ///
    /// * `writer`: the writer
    /// * `translation_unit`: the translation unit
    ///
    /// returns: Result<(), Error> - error if the writer fails to write
    pub fn emit_to_writer(
        mut self,
        writer: &mut io::BufWriter<fs::File>,
        translation_unit: BoundTranslationUnit,
        emit_debug_info: bool,
    ) -> io::Result<()> {
        self.emit_translation_unit(&translation_unit);

        let mut pc = 0;
        for instruction in &self.code {
            match instruction {
                Instruction::Load { level, offset } => {
                    writer.write_all(format!("{pc} LOD {level} {offset}\r\n").as_bytes())?;
                }
                Instruction::Store { level, offset } => {
                    writer.write_all(format!("{pc} STO {level} {offset}\r\n").as_bytes())?;
                }
                Instruction::Literal { value } => {
                    writer.write_all(format!("{pc} LIT 0 {value}\r\n").as_bytes())?;
                }
                Instruction::Jump { address } => {
                    writer.write_all(
                        format!("{pc} JMP 0 {}\r\n", self.resolve(address)).as_bytes(),
                    )?;
                }
                Instruction::Jmc { address } => {
                    writer.write_all(
                        format!("{pc} JMC 0 {}\r\n", self.resolve(address)).as_bytes(),
                    )?;
                }
                Instruction::Call { level, address } => {
                    writer.write_all(
                        format!("{pc} CAL {level} {}\r\n", self.resolve(address)).as_bytes(),
                    )?;
                }
                Instruction::Operation { operation } => {
                    writer.write_all(format!("{pc} OPR 0 {}\r\n", *operation as u32).as_bytes())?;
                }
                Instruction::Return => {
                    writer.write_all(format!("{pc} RET 0 0\r\n").as_bytes())?;
                }
                Instruction::Int { size } => {
                    writer.write_all(format!("{pc} INT 0 {size}\r\n").as_bytes())?;
                }
                Instruction::Dbg { debug_keyword } => {
                    pc -= 1;
                    if emit_debug_info {
                        match debug_keyword {
                            DebugKeyword::Registers => {
                                writer.write_all(b"&REGS\r\n")?;
                            }
                            DebugKeyword::Stack => {
                                writer.write_all(b"&STK\r\n")?;
                            }
                            DebugKeyword::StackA => {
                                writer.write_all(b"&STKA\r\n")?;
                            }
                            DebugKeyword::StackRg { start, end } => {
                                writer.write_all(format!("&STKRG {start} {end}\r\n").as_bytes())?;
                            }
                            DebugKeyword::StackN { amount } => {
                                writer.write_all(format!("&STKN {amount}\r\n").as_bytes())?;
                            }
                            DebugKeyword::Echo { message } => {
                                writer.write_all(format!("&ECHO {message}\r\n").as_bytes())?;
                            }
                        }
                    }
                }
                Instruction::Pld => writer.write_all(format!("{pc} PLD 0 0\r\n").as_bytes())?,
                Instruction::Sta => writer.write_all(format!("{pc} STA 0 0\r\n").as_bytes())?,
            }
            pc += 1;
        }
        Ok(())
    }

    fn resolve(&self, address: &Address) -> usize {
        match address {
            Address::Absolute(pc) => *pc,
            Address::Label(label) => *self
                .labels
                .get(label.as_str())
                .unwrap_or_else(|| panic!("Did not emit {label}")),
        }
    }

    fn emit_label(&mut self, label: String) {
        self.labels.insert(label, self.pc);
    }

    fn emit_int(&mut self, size: i32) {
        self.emit_instruction(Instruction::Int { size })
    }

    fn create_stack_frame(&mut self, size: usize) {
        self.emit_instruction(Instruction::Int { size: size as i32 })
    }

    fn emit_instruction(&mut self, instruction: Instruction) {
        match instruction {
            Instruction::Dbg { .. } => {}
            _ => self.pc += 1,
        };
        self.code.push(instruction);
    }

    fn emit_operation(&mut self, operation: OperationType) {
        self.emit_instruction(Instruction::Operation { operation });
    }

    fn load(&mut self, level: usize, offset: i32, size: usize) {
        for i in 0..size {
            self.emit_instruction(Instruction::Load {
                level,
                offset: offset + i as i32,
            });
        }
    }

    fn store(&mut self, level: usize, offset: i32, size: usize) {
        // Store in reverse order
        // i.e. variable of size 4, for example 4 integers a, b, c, d: at the top of the stack
        // is d. after storing there's c, then b and then a.
        // In memory it's stored as [a|b|c|d] for easy access to structs and arrays for example.
        for i in (0..size).rev() {
            self.emit_instruction(Instruction::Store {
                level,
                offset: offset + i as i32,
            });
        }
    }

    fn create_function_label(function_ident: usize) -> String {
        format!("f{function_ident}")
    }

    fn create_control_label(&mut self) -> String {
        let control_label = format!("c{}", self.control_statement_count);
        self.control_statement_count += 1;
        control_label
    }

    fn echo(&mut self, message: &str) {
        self.emit_debug_info(DebugKeyword::Echo {
            message: String::from(message),
        });
    }

    fn emit_jump(&mut self, address: Address) {
        self.emit_instruction(Instruction::Jump { address });
    }

    fn emit_jmc(&mut self, address: Address) {
        self.emit_instruction(Instruction::Jmc { address });
    }

    fn emit_debug_info(&mut self, debug_keyword: DebugKeyword) {
        self.emit_instruction(Instruction::Dbg { debug_keyword });
    }

    fn emit_call(&mut self, level: usize, address: Address) {
        self.emit_instruction(Instruction::Call { level, address });
    }

    fn emit_value(&mut self, value: &BoundLiteralValue) {
        fn emit_literal(emitter: &mut Emitter<'_, '_>, value: i32) {
            emitter.emit_instruction(Instruction::Literal { value })
        }

        match value {
            BoundLiteralValue::Pp(pp) => {
                emit_literal(self, *pp);
            }
            BoundLiteralValue::Flaccid(a, b) => {
                emit_literal(self, *a);
                emit_literal(self, *b);
            }
            BoundLiteralValue::AB(a, b) => {
                emit_literal(self, *a);
                emit_literal(self, *b);
            }
            BoundLiteralValue::P(p) => {
                emit_literal(self, *p as i32);
            }
            BoundLiteralValue::Booba(booba) => {
                emit_literal(self, *booba as i32);
            }
            BoundLiteralValue::Yarn(_yarn) => {
                todo!("Not yet implemented");
            }
        }
    }
}

mod error_diagnosis {
    use std::{cmp, error, fmt};

    pub struct SyntaxError {
        error_messages: Vec<String>,
    }

    impl SyntaxError {
        pub fn new(error_messages: Vec<String>) -> Self {
            SyntaxError { error_messages }
        }
    }

    impl fmt::Debug for SyntaxError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            writeln!(f, "Syntax error")?;
            for error_message in &self.error_messages {
                writeln!(f, "{error_message}")?;
            }
            Ok(())
        }
    }

    impl fmt::Display for SyntaxError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Syntax error")
        }
    }

    impl error::Error for SyntaxError {}

    #[derive(Clone, Debug, Eq, PartialEq)]
    pub struct ErrorMessage {
        row: u32,
        col: u32,
        message: String,
    }

    impl ErrorMessage {
        pub fn new(row: u32, col: u32, message: String) -> Self {
            ErrorMessage { row, col, message }
        }
        pub fn message(&self) -> &str {
            &self.message
        }
    }

    impl Ord for ErrorMessage {
        fn cmp(&self, other: &Self) -> cmp::Ordering {
            self.row
                .cmp(&other.row)
                .then_with(|| self.col.cmp(&other.col))
        }
    }

    impl PartialOrd for ErrorMessage {
        fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
}

mod lexer {
    use std::fmt;

    use dpp_macros_derive::Pos;

    use dpp_macros::Pos;

    #[derive(Debug, Pos)]
    pub struct Token<'a> {
        /// The kind of the token.
        kind: TokenKind,
        /// Row, Column
        position: (u32, u32),
        /// The value of the token. The reason we don't use Option here is because
        /// inside the parser in the method `expect` we return an Option on the value.
        /// If the value is None that means the parser panics - the parsing is stopped,
        /// tokens are consumed until it's synchronized. Note that it does not matter we
        /// use Option there, there could be Result as well.
        value: &'a str,
    }

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum TokenKind {
        Identifier, // identifier
        Literal(LiteralKind),
        BangEqual,          // !=
        Comment,            // #
        Whitespace,         //
        Eof,                // EOF
        Unknown,            // idk
        EqualEqual,         // ==
        Equal,              // =
        Bang,               // !
        Star,               // *
        ForwardSlash,       // /
        BackSlash,          // \
        Plus,               // +
        MinusEqual,         // -=
        PlusEqual,          // +=
        PlusDash,           // +-
        Dash,               // -
        Greater,            // >
        GreaterEqual,       // >=
        Less,               // <
        LessEqual,          // <=
        NomKeyword,         // nom
        YemKeyword,         // yem
        OpenParen,          // (
        CloseParen,         // )
        OpenBrace,          // {
        CloseBrace,         // }
        OpenBracket,        // [
        CloseBracket,       // ]
        Colon,              // :
        Semicolon,          // ;
        Ampersand,          // &
        Pipe,               // |
        Dot,                // .
        Comma,              // ,
        IfKeyword,          // if
        LetKeyword,         // let
        ByeKeyword,         // return
        FUNcKeyword,        // function
        PprintKeyword,      // write()
        PprintlnKeyword,    // writeln()
        PpanicKeyword,      // panic()
        PpinKeyword,        // read()
        PpKeyword,          // i32
        FlaccidKeyword,     // float
        PKeyword,           // char
        ABKeyword,          // ratio
        BoobaKeyword,       // bool
        NoppKeyword,        // void
        YarnKeyword,        // String
        ForKeyword,         // for
        ElseKeyword,        // else
        DoubleQuote,        // "
        ToKeyword,          // to
        Arrow,              // ->
        WhileKeyword,       // while
        DoKeyword,          // do
        LoopKeyword,        // loop
        BreakKeyword,       // break
        ContinueKeyword,    // continue
        CaseKeyword,        // case
        SwitchKeyword,      // switch
        StructKeyword,      // struct / record
        PipePipe,           // ||
        AmpersandAmpersand, // &&
        ConstKeyword,
        NewKeyword,
    }

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum LiteralKind {
        Pp,
        Flaccid,
        AB,
        P,
        Yarn,
    }

    impl<'a> Token<'a> {
        pub fn new(kind: TokenKind, position: (u32, u32), value: &'a str) -> Self {
            Token {
                kind,
                position,
                value,
            }
        }

        #[must_use]
        pub fn value(&self) -> &'a str {
            self.value
        }

        #[must_use]
        pub const fn kind(&self) -> TokenKind {
            self.kind
        }
    }

    impl fmt::Display for Token<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{} ({})", self.value, self.kind)
        }
    }

    impl fmt::Display for TokenKind {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let text_representation = match self {
                Self::Identifier => "identifier",
                Self::BangEqual => "\"!=\"",
                Self::Comment | Self::Whitespace | Self::Eof | Self::Unknown => "",
                Self::EqualEqual => "\"==\"",
                Self::Equal => "\"=\"",
                Self::Bang => "\"!\"",
                Self::Star => "\"*\"",
                Self::ForwardSlash => "\"/\"",
                Self::BackSlash => "\"\\\"",
                Self::Plus => "\"+\"",
                Self::MinusEqual => "\"-=\"",
                Self::PlusEqual => "\"+=\"",
                Self::PlusDash => "\"+-\"",
                Self::Dash => "\"-\"",
                Self::Greater => "\">\"",
                Self::GreaterEqual => "\">=\"",
                Self::Less => "\"<\"",
                Self::LessEqual => "\"<=\"",
                Self::NomKeyword => "\"nom\"",
                Self::NewKeyword => "\"new\"",
                Self::YemKeyword => "\"yem\"",
                Self::OpenParen => "\"(\"",
                Self::CloseParen => "\")\"",
                Self::OpenBrace => "\"{\"",
                Self::CloseBrace => "\"}\"",
                Self::OpenBracket => "\"[\"",
                Self::CloseBracket => "\"]\"",
                Self::Colon => "\":\"",
                Self::Semicolon => "\";\"",
                Self::Ampersand => "\"&\"",
                Self::AmpersandAmpersand => "\"&&\"",
                Self::Pipe => "\"|\"",
                Self::PipePipe => "\"||\"",
                Self::Comma => "\",\"",
                Self::IfKeyword => "\"if\"",
                Self::ConstKeyword => "\"const\"",
                Self::LetKeyword => "\"let\"",
                Self::ByeKeyword => "\"bye\"",
                Self::PprintKeyword => "\"pprint\"",
                Self::PprintlnKeyword => "\"pprintln\"",
                Self::PpanicKeyword => "\"ppanic\"",
                Self::PpinKeyword => "\"ppin\"",
                Self::FUNcKeyword => "\"FUNc\"",
                Self::ElseKeyword => "\"else\"",
                Self::ForKeyword => "\"for\"",
                Self::PpKeyword => "data type \"pp\"",
                Self::FlaccidKeyword => "data type \"flaccid\"",
                Self::ABKeyword => "data type \"ab\"",
                Self::PKeyword => "data type \"p\"",
                Self::BoobaKeyword => "data type \"booba\"",
                Self::NoppKeyword => "void data type \"nopp\"",
                Self::YarnKeyword => "data type \"yarn\"",
                Self::DoubleQuote => "\"\"\"",
                Self::ToKeyword => "\"to\"",
                Self::Arrow => "\"->\"",
                Self::WhileKeyword => "\"while\"",
                Self::DoKeyword => "\"do\"",
                Self::LoopKeyword => "\"loop\"",
                Self::BreakKeyword => "\"break\"",
                Self::ContinueKeyword => "\"continue\"",
                Self::SwitchKeyword => "\"switch\"",
                Self::StructKeyword => "\"struct\"",
                Self::CaseKeyword => "\"case\"",
                Self::Literal(literal_kind) => {
                    return write!(f, "{literal_kind}");
                }
                Self::Dot => "\".\"",
            };
            write!(f, "{text_representation}")
        }
    }

    impl fmt::Display for LiteralKind {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                LiteralKind::Pp => write!(f, "pp"),
                LiteralKind::Flaccid => write!(f, "flaccid"),
                LiteralKind::P => write!(f, "p"),
                LiteralKind::Yarn => write!(f, "yarn"),
                LiteralKind::AB => write!(f, "ab"),
            }
        }
    }
}

mod parser {
    use std::fmt;

    use dpp_macros_derive::Pos;

    use dpp_macros::Pos;

    #[derive(Clone, Debug, Pos)]
    pub struct TranslationUnit<'a> {
        position: (u32, u32),
        functions: Vec<Function<'a>>,
        global_statements: Vec<Statement<'a>>,
        struct_declarations: Vec<Struct<'a>>,
    }

    #[derive(Clone, Debug, Pos)]
    pub struct Function<'a> {
        position: (u32, u32),
        identifier: &'a str,
        return_type: DataType,
        parameters: Vec<Variable<'a>>,
        statements: Vec<Statement<'a>>,
    }

    #[derive(Clone, Debug, Pos)]
    pub struct Block<'a> {
        position: (u32, u32),
        statements: Vec<Statement<'a>>,
    }

    #[derive(Clone, Debug, Pos)]
    pub enum Statement<'a> {
        VariableDeclaration {
            position: (u32, u32),
            variable: Variable<'a>,
            value: Option<Expression<'a>>,
        },
        If {
            position: (u32, u32),
            expression: Expression<'a>,
            statement: Box<Statement<'a>>,
        },
        IfElse {
            position: (u32, u32),
            expression: Expression<'a>,
            statement: Box<Statement<'a>>,
            else_statement: Box<Statement<'a>>,
        },
        Bye {
            position: (u32, u32),
            expression: Option<Expression<'a>>,
        },
        Print {
            position: (u32, u32),
            print_function: fn(&str),
            expression: Expression<'a>,
        },
        Block {
            position: (u32, u32),
            block: Box<Block<'a>>,
        },
        Expression {
            position: (u32, u32),
            expression: Expression<'a>,
        },
        Empty {
            position: (u32, u32),
        },
        For {
            position: (u32, u32),
            index_ident: &'a str,
            ident_expression: Option<Expression<'a>>,
            length_expression: Expression<'a>,
            statement: Box<Statement<'a>>,
        },
        While {
            position: (u32, u32),
            expression: Expression<'a>,
            statement: Box<Statement<'a>>,
        },
        DoWhile {
            position: (u32, u32),
            statement: Box<Statement<'a>>,
            expression: Expression<'a>,
        },
        Loop {
            position: (u32, u32),
            statement: Box<Statement<'a>>,
        },
        Break {
            position: (u32, u32),
        },
        Continue {
            position: (u32, u32),
        },
        Switch {
            position: (u32, u32),
            expression: Expression<'a>,
            cases: Vec<Case<'a>>,
        },
        Assignment {
            position: (u32, u32),
            identifier: &'a str,
            field_identifier: Option<&'a str>,
            array_index_expression: Option<Expression<'a>>,
            expression: Expression<'a>,
        },
    }

    #[derive(Clone, Debug, Pos, PartialEq)]
    pub struct Variable<'a> {
        position: (u32, u32),
        identifier: &'a str,
        modifiers: Vec<Modifier>,
        data_type: DataType,
        pointer_count: usize,
        array_size_expr: Option<Expression<'a>>,
    }

    #[derive(Clone, Debug, Pos)]
    pub struct Case<'a> {
        position: (u32, u32),
        expression: Expression<'a>,
        block: Box<Block<'a>>,
    }

    #[derive(Eq, Hash, Debug, Clone)]
    pub enum DataType {
        Pp,
        // int
        AB,
        // ratio
        Flaccid,
        // float
        P,
        // char
        Yarn,
        // string
        Booba,
        // bool
        Nopp,
        // void
        Ratio,
        // ratio
        Struct(String),
        // struct
        Array(Box<DataType>, usize), // array with inner data type and size
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum Modifier {
        Const,
    }

    #[derive(Clone, Debug, PartialEq, Pos)]
    pub struct Struct<'a> {
        position: (u32, u32),
        fields: Vec<Variable<'a>>,
        ident: &'a str,
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum LiteralValue<'a> {
        Pp(i32),
        Flaccid(i32, i32),
        AB(i32, i32),
        P(char),
        Booba(bool),
        Yarn(&'a str),
    }

    #[derive(Clone, Debug, Pos, PartialEq)]
    pub struct StructFieldAssignment<'a> {
        position: (u32, u32),
        expression: Expression<'a>,
    }

    impl<'a> StructFieldAssignment<'a> {
        pub fn new(position: (u32, u32), expression: Expression<'a>) -> Self {
            Self {
                position,
                expression,
            }
        }

        pub fn position(&self) -> (u32, u32) {
            self.position
        }
        pub fn expression(&self) -> &Expression<'a> {
            &self.expression
        }
    }

    #[derive(Clone, Debug, Pos, PartialEq)]
    pub enum Expression<'a> {
        Literal {
            position: (u32, u32),
            value: LiteralValue<'a>,
        },
        Unary {
            position: (u32, u32),
            op: UnaryOperator,
            operand: Box<Expression<'a>>,
        },
        Binary {
            position: (u32, u32),
            lhs: Box<Expression<'a>>,
            op: BinaryOperator,
            rhs: Box<Expression<'a>>,
        },
        Identifier {
            position: (u32, u32),
            identifier: &'a str,
        },
        FunctionCall {
            position: (u32, u32),
            identifier: &'a str,
            arguments: Vec<Expression<'a>>,
        },
        Struct {
            position: (u32, u32),
            identifier: &'a str,
            field_assignments: Vec<StructFieldAssignment<'a>>,
        },
        StructFieldAccess {
            position: (u32, u32),
            identifiers: Vec<&'a str>,
        },
        ArrayAccess {
            position: (u32, u32),
            identifier: &'a str,
            array_index_expression: Box<Expression<'a>>,
        },
        Invalid {
            position: (u32, u32),
        },
    }

    #[derive(Eq, Clone, PartialEq, Debug)]
    pub enum BinaryOperator {
        Add,
        And,
        Or,
        Subtract,
        Multiply,
        Divide,
        NotEqual,
        Equal,
        GreaterThan,
        GreaterThanOrEqual,
        LessThan,
        LessThanOrEqual,
    }

    #[derive(Eq, Clone, PartialEq, Debug)]
    pub enum UnaryOperator {
        Not,
        Negate,
    }

    impl<'a> TranslationUnit<'a> {
        pub fn new(
            functions: Vec<Function<'a>>,
            global_statements: Vec<Statement<'a>>,
            struct_declarations: Vec<Struct<'a>>,
        ) -> Self {
            TranslationUnit {
                position: (1, 1),
                functions,
                global_statements,
                struct_declarations,
            }
        }

        pub fn functions(&self) -> &Vec<Function<'a>> {
            &self.functions
        }
        pub fn global_statements(&self) -> &Vec<Statement<'a>> {
            &self.global_statements
        }

        pub fn position(&self) -> (u32, u32) {
            self.position
        }
        pub fn struct_declarations(&self) -> &Vec<Struct<'a>> {
            &self.struct_declarations
        }
    }

    impl<'a> Function<'a> {
        pub fn new(
            position: (u32, u32),
            identifier: &'a str,
            return_type: DataType,
            parameters: Vec<Variable<'a>>,
            statements: Vec<Statement<'a>>,
        ) -> Self {
            Function {
                position,
                identifier,
                return_type,
                parameters,
                statements,
            }
        }

        pub fn identifier(&self) -> &'a str {
            self.identifier
        }
        pub fn return_type(&self) -> &DataType {
            &self.return_type
        }
        pub fn statements(&self) -> &Vec<Statement<'a>> {
            &self.statements
        }
        pub fn parameters(&self) -> &Vec<Variable<'a>> {
            &self.parameters
        }
    }

    impl<'a> Block<'a> {
        pub fn new(position: (u32, u32), statements: Vec<Statement<'a>>) -> Self {
            Block {
                position,
                statements,
            }
        }

        pub fn position(&self) -> (u32, u32) {
            self.position
        }
        pub fn statements(&self) -> &Vec<Statement<'a>> {
            &self.statements
        }
    }

    impl<'a> Variable<'a> {
        pub fn new(
            position: (u32, u32),
            identifier: &'a str,
            data_type: DataType,
            modifiers: Vec<Modifier>,
            pointer_count: usize,
            array_size_expr: Option<Expression<'a>>,
        ) -> Self {
            Variable {
                position,
                identifier,
                modifiers,
                data_type,
                pointer_count,
                array_size_expr,
            }
        }

        pub fn position(&self) -> (u32, u32) {
            self.position
        }
        pub fn identifier(&self) -> &'a str {
            self.identifier
        }
        pub fn data_type(&self) -> &DataType {
            &self.data_type
        }
        pub fn modifiers(&self) -> &Vec<Modifier> {
            &self.modifiers
        }
        pub fn has_modifier(&self, modifier: Modifier) -> bool {
            self.modifiers.contains(&modifier)
        }
        pub fn pointer_count(&self) -> usize {
            self.pointer_count
        }
        pub fn array_size_expr(&self) -> &Option<Expression<'a>> {
            &self.array_size_expr
        }
    }

    impl<'a> Case<'a> {
        pub fn new(
            position: (u32, u32),
            expression: Expression<'a>,
            block: Box<Block<'a>>,
        ) -> Self {
            Case {
                position,
                expression,
                block,
            }
        }

        pub fn expression(&self) -> &Expression<'a> {
            &self.expression
        }
        pub fn block(&self) -> &Box<Block<'a>> {
            &self.block
        }
    }

    impl<'a> Struct<'a> {
        pub fn new(position: (u32, u32), ident: &'a str, fields: Vec<Variable<'a>>) -> Self {
            Self {
                position,
                ident,
                fields,
            }
        }

        pub fn fields(&self) -> &Vec<Variable<'a>> {
            &self.fields
        }
        pub fn ident(&self) -> &str {
            self.ident
        }
    }

    impl fmt::Display for Expression<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let formatted = match self {
                Expression::Literal { value, .. } => value.to_string(),
                Expression::Unary { operand, op, .. } => {
                    format!("Unary expression {}{}", op, operand)
                }
                Expression::Binary { .. } => "Binary expression".to_string(),
                Expression::Identifier { identifier, .. } => (*identifier).to_string(),
                Expression::FunctionCall { identifier, .. } => {
                    format!("Function {identifier}")
                }
                Expression::Invalid { .. } => "Invalid expression".to_string(),
                Expression::Struct { identifier, .. } => format!("Struct {identifier}"),
                Expression::StructFieldAccess { identifiers, .. } => {
                    format!("Struct field access {}", identifiers.join("."))
                }
                Expression::ArrayAccess {
                    identifier,
                    array_index_expression,
                    ..
                } => format!("{identifier}[{array_index_expression}]"),
            };
            write!(f, "{}", formatted)?;
            Ok(())
        }
    }

    impl fmt::Display for LiteralValue<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                LiteralValue::Pp(pp) => write!(f, "{pp}"),
                LiteralValue::Flaccid(a, b) => write!(f, "{a}.{b}"),
                LiteralValue::AB(a, b) => write!(f, "{a}|{b}"),
                LiteralValue::P(p) => write!(f, "{p}"),
                LiteralValue::Booba(booba) => write!(f, "{booba}"),
                LiteralValue::Yarn(yarn) => write!(f, "{yarn}"),
            }
        }
    }

    impl PartialEq for DataType {
        fn eq(&self, other: &Self) -> bool {
            matches!(
                (self, other),
                (DataType::Pp, DataType::Pp)
                    | (DataType::P, DataType::P)
                    | (DataType::Flaccid, DataType::Flaccid)
                    | (DataType::AB, DataType::AB)
                    | (DataType::Yarn, DataType::Yarn)
                    | (DataType::Booba, DataType::Booba)
                    | (DataType::Nopp, DataType::Nopp)
            )
        }
    }

    impl fmt::Display for DataType {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                DataType::Pp => write!(f, "integer"),
                DataType::Flaccid => write!(f, "flaccid"),
                DataType::P => write!(f, "p"),
                DataType::Yarn => write!(f, "yarn"),
                DataType::Booba => write!(f, "booba"),
                DataType::Nopp => write!(f, "nopp"),
                DataType::Ratio => write!(f, "ratio"),
                DataType::Struct(name) => write!(f, "struct {name}"),
                DataType::AB => write!(f, "ratio"),
                DataType::Array(inner, size) => write!(f, "{inner}[{size}]"),
            }
        }
    }

    impl fmt::Display for UnaryOperator {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                UnaryOperator::Not => write!(f, "!"),
                UnaryOperator::Negate => write!(f, "-"),
            }
        }
    }
}

mod analysis {
    use std::fmt::Formatter;
    use std::{cmp, collections, fmt, ops};

    use crate::parse::parser::{BinaryOperator, DataType, Modifier, UnaryOperator};

    #[derive(Clone, Debug, PartialEq)]
    pub struct SymbolTable<'a> {
        /// Current stack of function scopes.
        scopes: Vec<Scope<'a>>,
        /// The global ID counter.
        guid_counter: usize,
        /// The context that contains the current function id etc.
        context: Context<'a>,
    }

    #[derive(Clone, Debug, PartialEq, Eq, Default)]
    pub struct Context<'a> {
        current_function: Option<&'a str>,
        current_variable_id: Option<usize>,
        current_struct_id: Option<usize>,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct Scope<'a> {
        /// Variable declaration symbol table.
        variable_declarations: collections::HashMap<&'a str, VariableDeclarationDescriptor>,
        /// Function definition symbol table.
        function_definitions: collections::HashMap<&'a str, FunctionDefinitionDescriptor>,
        /// Struct definition symbol table.
        struct_definitions: collections::HashMap<&'a str, StructDefinitionDescriptor>,
        /// The current stack position of the scope.
        stack_position: usize,
        /// The identifier of this function scope (i.e. the function identifier).
        function_identifier: Option<&'a str>,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct StructDefinitionDescriptor {
        id: usize,
        size: usize,
        // Offset + data type.
        fields: Vec<BoundStructField>,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct VariableDeclarationDescriptor {
        id: usize,
        stack_position: usize,
        data_type: BoundDataType,
        modifiers: Vec<Modifier>,
        value: Option<BoundExpression>,
        is_parameter: bool,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct FunctionDefinitionDescriptor {
        id: usize,
        return_type: BoundDataType,
        parameters: Vec<BoundVariable>,
        stack_frame_size: usize,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct BoundTranslationUnit {
        pub functions: Vec<BoundFunction>,
        main_function_identifier: usize,
        global_stack_frame_size: usize,
        pub global_variable_assignments: Vec<BoundStatement>,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct BoundFunction {
        identifier: usize,
        is_main_function: bool,
        stack_frame_size: usize,
        return_size: usize,
        parameters: Vec<BoundVariable>,
        pub statements: Vec<BoundStatement>,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct BoundVariableAssignment {
        pub variable: BoundVariable,
        pub value: BoundExpression,
    }

    #[derive(Eq, Clone, PartialEq, Debug)]
    pub enum BoundLiteralValue {
        Pp(i32),
        Flaccid(i32, i32),
        AB(i32, i32),
        P(char),
        Booba(bool),
        Yarn(String),
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct BoundStructField {
        modifiers: Vec<Modifier>,
        data_type: BoundDataType,
        ident: String,
        offset: usize,
    }

    #[derive(Eq, Clone, PartialEq, Debug)]
    pub enum BoundExpression {
        Literal(BoundLiteralValue),
        Unary {
            op: UnaryOperator,
            operand: Box<BoundExpression>,
        },
        Binary {
            lhs: Box<BoundExpression>,
            op: BinaryOperator,
            rhs: Box<BoundExpression>,
        },
        Variable(BoundVariable),
        FunctionCall {
            level: usize,
            identifier: usize,
            return_type_size: usize,
            arguments_size: usize,
            arguments: Vec<BoundExpression>,
        },
        Struct(Vec<BoundStructFieldAssignment>),
        StructFieldAccess(BoundVariable),
        ArrayAccess(BoundVariable, usize),
    }

    #[derive(Eq, PartialEq, Clone, Debug)]
    pub struct BoundStructFieldAssignment {
        expression: BoundExpression,
    }

    impl BoundStructFieldAssignment {
        pub fn new(expression: BoundExpression) -> Self {
            Self { expression }
        }
        pub fn expression(&self) -> &BoundExpression {
            &self.expression
        }
    }

    #[derive(Eq, PartialEq, Clone, Debug)]
    pub struct BoundVariable {
        position: BoundVariablePosition,
        data_type: BoundDataType,
        is_const: bool,
    }

    #[derive(Eq, PartialEq, Clone, Debug)]
    pub enum BoundVariablePosition {
        Static(usize, i32),
        Dynamic(usize, i32, Box<BoundExpression>),
    }

    impl fmt::Display for BoundVariablePosition {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            match self {
                BoundVariablePosition::Static(level, offset) => write!(
                    f,
                    "level: {level}, \
                offset: {offset}"
                ),
                BoundVariablePosition::Dynamic(level, base_offset, dynamic_offset) => write!(
                    f,
                    "level: {level}, \
                base offset: {base_offset}, dynamic offset: {dynamic_offset:?}"
                ),
            }
        }
    }

    #[derive(PartialEq, Eq, Hash, Debug, Clone)]
    pub enum BoundDataType {
        Pp,
        // int
        AB,
        // ratio
        Flaccid,
        // float
        P,
        // char
        Yarn,
        // string
        Booba,
        // bool
        Nopp,
        // void
        Ratio,
        // ratio
        Struct(String, usize),
        // struct name with size
        Array(Box<BoundDataType>, usize), // array with inner data type and array size
    }

    impl fmt::Display for BoundDataType {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                BoundDataType::Pp => write!(f, "integer"),
                BoundDataType::Flaccid => write!(f, "flaccid"),
                BoundDataType::P => write!(f, "p"),
                BoundDataType::Yarn => write!(f, "yarn"),
                BoundDataType::Booba => write!(f, "booba"),
                BoundDataType::Nopp => write!(f, "nopp"),
                BoundDataType::Ratio => write!(f, "ratio"),
                BoundDataType::Struct(name, _) => write!(f, "struct {name}"),
                BoundDataType::AB => write!(f, "ratio"),
                BoundDataType::Array(inner, size) => write!(f, "{inner}[{size}]"),
            }
        }
    }

    #[derive(Clone, PartialEq, Debug)]
    pub enum BoundStatement {
        If {
            expression: BoundExpression,
            statement: Box<BoundStatement>,
        },
        IfElse {
            expression: BoundExpression,
            statement: Box<BoundStatement>,
            else_statement: Box<BoundStatement>,
        },
        Bye {
            expression: Option<BoundExpression>,
            return_type_size: usize,
        },
        Print {
            print_function: fn(&str),
            expression: BoundExpression,
        },
        Expression(BoundExpression),
        For {
            variable: BoundVariable,
            ident_expression: Option<BoundExpression>,
            length_expression: BoundExpression,
            statement: Box<BoundStatement>,
        },
        While {
            expression: BoundExpression,
            statement: Box<BoundStatement>,
        },
        DoWhile {
            expression: BoundExpression,
            statement: Box<BoundStatement>,
        },
        Loop {
            statement: Box<BoundStatement>,
        },
        Break,
        Continue,
        Switch {
            expression: BoundExpression,
            cases: Vec<BoundCase>,
        },
        VariableAssignment(BoundVariableAssignment),
        Statements(Vec<BoundStatement>),
        Empty,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct BoundCase {
        pub expression: BoundExpression,
        pub statements: Vec<BoundStatement>,
    }

    impl BoundDataType {
        pub fn size(&self) -> usize {
            match self {
                BoundDataType::Pp => 1,
                BoundDataType::AB => 2,
                BoundDataType::Flaccid => 1,
                BoundDataType::P => 1,
                BoundDataType::Yarn => todo!("Yarn not yet implemented"),
                BoundDataType::Booba => 1,
                BoundDataType::Nopp => 0,
                BoundDataType::Ratio => 2,
                BoundDataType::Struct(_, size) => *size,
                BoundDataType::Array(data_type, size) => data_type.size() * size,
            }
        }
    }

    impl<'a> SymbolTable<'a> {
        pub fn new() -> Self {
            Self {
                scopes: vec![Scope::new(None, Scope::ACTIVATION_RECORD_SIZE)],
                context: Context::default(),
                guid_counter: 0,
            }
        }

        pub fn next_id(&mut self) -> usize {
            let current_id = self.guid_counter;
            self.guid_counter += 1;
            current_id
        }

        pub fn current_scope(&self) -> &Scope<'a> {
            self.scopes.last().expect("A scope")
        }

        pub fn current_scope_mut(&mut self) -> &mut Scope<'a> {
            self.scopes.last_mut().expect("A scope")
        }

        pub fn current_scope_depth(&self) -> usize {
            self.scopes.len()
        }

        pub fn declare_variable(
            &mut self,
            modifiers: Vec<Modifier>,
            data_type: BoundDataType,
            ident: &'a str,
            is_parameter: bool,
        ) {
            let id = self.next_id();
            self.current_scope_mut().declare_variable(
                id,
                modifiers,
                data_type,
                ident,
                is_parameter,
            );
            let stack_position = self.current_scope().stack_position;
            if let Some(function) = self.current_function_mut() {
                function.update_stack_frame_size(stack_position);
            }
        }

        pub fn define_struct(&mut self, ident: &'a str, fields: Vec<BoundStructField>) {
            let id = self.next_id();
            self.current_scope_mut().define_struct(ident, id, fields);
        }

        pub fn define_function(
            &mut self,
            return_type: BoundDataType,
            ident: &'a str,
            parameters: Vec<BoundVariable>,
        ) {
            let id = self.next_id();
            self.current_scope_mut()
                .define_function(ident, id, return_type, parameters);
        }

        pub fn current_function_mut(&mut self) -> Option<&mut FunctionDefinitionDescriptor> {
            self.scopes
                .iter_mut()
                .rev()
                .find(|scope| scope.function_identifier != self.context.current_function)?
                .get_function_mut(self.context.current_function?)
        }

        pub fn current_function(&self) -> Option<&FunctionDefinitionDescriptor> {
            self.find_function_definition(self.context.current_function?)
        }

        pub fn find_struct_definition(
            &self,
            identifier: &str,
        ) -> (usize, Option<&StructDefinitionDescriptor>) {
            self.find_in_scope(identifier, |scope, ident| {
                scope.get_struct_definition(ident)
            })
        }

        pub fn find_function_definition(
            &self,
            identifier: &str,
        ) -> Option<&FunctionDefinitionDescriptor> {
            self.scopes
                .iter()
                .rev()
                .find(|scope| scope.has_function(identifier))?
                .get_function(identifier)
        }

        pub fn find_variable_declaration(
            &self,
            identifier: &str,
        ) -> (usize, Option<&VariableDeclarationDescriptor>) {
            self.find_in_scope(identifier, |scope, ident| scope.get_variable(ident))
        }

        fn find_in_scope<'b: 'a, T>(
            &'b self,
            identifier: &str,
            getter: fn(&'a Scope<'a>, &str) -> Option<&'b T>,
        ) -> (usize, Option<&'b T>) {
            let mut level = 0;
            let mut cur = self.current_scope().function_identifier;
            for scope in self.scopes.iter().rev() {
                if cur != scope.function_identifier {
                    level += 1;
                }
                if let Some(variable) = getter(scope, identifier) {
                    return (level, Some(variable));
                }
                cur = scope.function_identifier;
            }

            // Variable does not exist.
            (0, None)
        }

        pub fn find_variable_mut(
            &mut self,
            identifier: &str,
        ) -> (usize, Option<&mut VariableDeclarationDescriptor>) {
            let mut level = 0;
            let mut cur = self.current_scope().function_identifier;
            for scope in self.scopes.iter_mut().rev() {
                if cur != scope.function_identifier {
                    level += 1;
                }
                if scope.get_variable(identifier).is_some() {
                    return (level, scope.get_variable_mut(identifier));
                }
                cur = scope.function_identifier;
            }

            // Variable does not exist.
            (0, None)
        }

        pub fn push_scope(&mut self) {
            self.push_scope_internal(
                self.context.current_function,
                self.scopes.last().expect("A scope").stack_position(),
            );
        }

        pub fn push_function_scope(&mut self, function_identifier: &'a str) {
            self.push_scope_internal(Some(function_identifier), Scope::ACTIVATION_RECORD_SIZE);
        }

        fn push_scope_internal(
            &mut self,
            function_identifier: Option<&'a str>,
            stack_position: usize,
        ) {
            self.scopes
                .push(Scope::new(function_identifier, stack_position));
            if let Some(function_identifier) = function_identifier {
                self.context.current_function = Some(function_identifier);
            }
        }

        pub fn pop_scope(&mut self) {
            self.scopes.pop();
            self.context.current_function = self.current_scope().function_identifier;
        }

        pub fn current_function_identifier(&self) -> Option<&'a str> {
            self.context.current_function
        }
    }

    impl<'a> Scope<'a> {
        pub const ACTIVATION_RECORD_SIZE: usize = 3;

        pub fn new(function_identifier: Option<&'a str>, stack_position: usize) -> Self {
            Self {
                variable_declarations: collections::HashMap::new(),
                function_definitions: collections::HashMap::new(),
                struct_definitions: collections::HashMap::new(),
                stack_position,
                function_identifier,
            }
        }

        fn define_struct(&mut self, identifier: &'a str, id: usize, fields: Vec<BoundStructField>) {
            self.struct_definitions
                .insert(identifier, StructDefinitionDescriptor::new(id, fields));
        }

        fn get_struct_definition(&self, identifier: &str) -> Option<&StructDefinitionDescriptor> {
            self.struct_definitions.get(identifier)
        }

        fn get_struct_definition_mut(
            &mut self,
            identifier: &str,
        ) -> Option<&mut StructDefinitionDescriptor> {
            self.struct_definitions.get_mut(identifier)
        }

        fn define_function(
            &mut self,
            identifier: &'a str,
            id: usize,
            return_type: BoundDataType,
            parameters: Vec<BoundVariable>,
        ) {
            self.function_definitions.insert(
                identifier,
                FunctionDefinitionDescriptor::new(id, return_type, parameters),
            );
        }

        pub fn get_function(&self, identifier: &str) -> Option<&FunctionDefinitionDescriptor> {
            self.function_definitions.get(identifier)
        }

        pub fn get_function_mut(
            &mut self,
            identifier: &str,
        ) -> Option<&mut FunctionDefinitionDescriptor> {
            self.function_definitions.get_mut(identifier)
        }

        pub fn has_function(&self, identifier: &str) -> bool {
            self.function_definitions.contains_key(identifier)
        }

        fn declare_variable(
            &mut self,
            id: usize,
            modifiers: Vec<Modifier>,
            data_type: BoundDataType,
            ident: &'a str,
            is_parameter: bool,
        ) {
            let variable_descriptor = VariableDeclarationDescriptor::new(
                id,
                self.stack_position,
                modifiers,
                data_type,
                is_parameter,
            );
            self.stack_position += variable_descriptor.data_type().size();
            self.variable_declarations
                .insert(ident, variable_descriptor);
        }

        pub fn get_variable(&self, identifier: &str) -> Option<&VariableDeclarationDescriptor> {
            self.variable_declarations.get(identifier)
        }

        pub fn get_variable_mut(
            &mut self,
            identifier: &str,
        ) -> Option<&mut VariableDeclarationDescriptor> {
            self.variable_declarations.get_mut(identifier)
        }

        pub fn stack_position(&self) -> usize {
            self.stack_position
        }
    }

    impl StructDefinitionDescriptor {
        pub fn new(id: usize, fields: Vec<BoundStructField>) -> Self {
            let size = fields.iter().map(|field| field.data_type().size()).sum();
            Self { id, fields, size }
        }

        pub fn id(&self) -> usize {
            self.id
        }
        pub fn fields(&self) -> &Vec<BoundStructField> {
            &self.fields
        }
        pub fn size(&self) -> usize {
            self.size
        }
    }

    impl VariableDeclarationDescriptor {
        pub fn new(
            id: usize,
            stack_position: usize,
            modifiers: Vec<Modifier>,
            data_type: BoundDataType,
            is_parameter: bool,
        ) -> Self {
            Self {
                id,
                stack_position,
                data_type,
                modifiers,
                value: None,
                is_parameter,
            }
        }

        pub fn stack_position(&self) -> usize {
            self.stack_position
        }
        pub fn data_type(&self) -> &BoundDataType {
            &self.data_type
        }
        pub fn has_modifier(&self, modifier: Modifier) -> bool {
            self.modifiers.contains(&modifier)
        }
    }

    #[derive(Debug)]
    pub struct BoundDataTypeError {
        pub reason: String,
        pub dummy_data_type: BoundDataType,
    }
    impl<'a> TryFrom<(&DataType, &SymbolTable<'a>)> for BoundDataType {
        type Error = BoundDataTypeError;
        fn try_from(value: (&DataType, &SymbolTable<'a>)) -> Result<Self, Self::Error> {
            match value.0 {
                DataType::Pp => Ok(BoundDataType::Pp),
                DataType::AB => Ok(BoundDataType::AB),
                DataType::Flaccid => Ok(BoundDataType::Flaccid),
                DataType::P => Ok(BoundDataType::P),
                DataType::Yarn => Ok(BoundDataType::Yarn),
                DataType::Booba => Ok(BoundDataType::Booba),
                DataType::Nopp => Ok(BoundDataType::Nopp),
                DataType::Ratio => Ok(BoundDataType::Ratio),
                DataType::Struct(name) => {
                    if let Some(a_struct) = value.1.find_struct_definition(name).1 {
                        return Ok(BoundDataType::Struct(name.clone(), a_struct.size()));
                    }
                    Err(BoundDataTypeError {
                        reason: format!("Unknown struct {name}"),
                        dummy_data_type: BoundDataType::Struct(name.clone(), 0),
                    })
                }
                DataType::Array(inner, size) => {
                    let inner = BoundDataType::try_from((&*inner.clone(), value.1))?;
                    Ok(BoundDataType::Array(Box::new(inner), *size))
                }
            }
        }
    }

    impl FunctionDefinitionDescriptor {
        pub fn new(id: usize, return_type: BoundDataType, parameters: Vec<BoundVariable>) -> Self {
            FunctionDefinitionDescriptor {
                id,
                return_type,
                parameters,
                stack_frame_size: Scope::ACTIVATION_RECORD_SIZE,
            }
        }

        pub fn update_stack_frame_size(&mut self, stack_frame_size: usize) {
            self.stack_frame_size = cmp::max(self.stack_frame_size, stack_frame_size);
        }

        pub fn return_type(&self) -> &BoundDataType {
            &self.return_type
        }
        pub fn parameters(&self) -> &Vec<BoundVariable> {
            &self.parameters
        }

        /// The size of parameters in instructions.
        pub fn parameters_size(&self) -> usize {
            self.parameters()
                .iter()
                .fold(0, |acc, parameter| acc + parameter.size())
        }
        pub fn id(&self) -> usize {
            self.id
        }
        pub fn stack_frame_size(&self) -> usize {
            self.stack_frame_size
        }
    }

    impl BoundTranslationUnit {
        pub fn new(
            functions: Vec<BoundFunction>,
            main_function_identifier: usize,
            global_stack_frame_size: usize,
            global_variable_assignments: Vec<BoundStatement>,
        ) -> Self {
            BoundTranslationUnit {
                functions,
                main_function_identifier,
                global_stack_frame_size,
                global_variable_assignments,
            }
        }

        pub fn functions(&self) -> &Vec<BoundFunction> {
            &self.functions
        }
        pub fn global_stack_frame_size(&self) -> usize {
            self.global_stack_frame_size
        }
        pub fn global_variable_assignments(&self) -> &Vec<BoundStatement> {
            &self.global_variable_assignments
        }

        pub fn main_function_identifier(&self) -> usize {
            self.main_function_identifier
        }
    }

    impl BoundFunction {
        pub fn new(
            identifier: usize,
            stack_frame_size: usize,
            is_main_function: bool,
            return_size: usize,
            parameters: Vec<BoundVariable>,
            statements: Vec<BoundStatement>,
        ) -> Self {
            Self {
                identifier,
                stack_frame_size,
                is_main_function,
                return_size,
                parameters,
                statements,
            }
        }

        pub fn identifier(&self) -> usize {
            self.identifier
        }
        pub fn stack_frame_size(&self) -> usize {
            self.stack_frame_size
        }
        pub fn statements(&self) -> &Vec<BoundStatement> {
            &self.statements
        }
        pub fn parameters(&self) -> &Vec<BoundVariable> {
            &self.parameters
        }
        pub fn return_size(&self) -> usize {
            self.return_size
        }
        pub fn is_main_function(&self) -> bool {
            self.is_main_function
        }
    }

    impl BoundVariableAssignment {
        pub fn new(variable: BoundVariable, value: BoundExpression) -> Self {
            BoundVariableAssignment { variable, value }
        }
        pub fn variable(&self) -> &BoundVariable {
            &self.variable
        }
        pub fn value(&self) -> &BoundExpression {
            &self.value
        }
    }

    impl BoundVariable {
        pub fn with_dynamic_position(
            level: usize,
            base_offset: i32,
            dynamic_offset: BoundExpression,
            data_type: BoundDataType,
            is_const: bool,
        ) -> Self {
            BoundVariable {
                position: BoundVariablePosition::Dynamic(
                    level,
                    base_offset,
                    Box::new(dynamic_offset),
                ),
                data_type,
                is_const,
            }
        }

        pub fn with_static_position(
            level: usize,
            offset: i32,
            data_type: BoundDataType,
            is_const: bool,
        ) -> Self {
            BoundVariable {
                position: BoundVariablePosition::Static(level, offset),
                data_type,
                is_const,
            }
        }

        pub fn position(&self) -> &BoundVariablePosition {
            &self.position
        }

        pub fn is_const(&self) -> bool {
            self.is_const
        }

        pub fn data_type(&self) -> &BoundDataType {
            &self.data_type
        }

        pub fn size(&self) -> usize {
            self.data_type.size()
        }
    }

    impl BoundCase {
        pub fn new(expression: BoundExpression, statements: Vec<BoundStatement>) -> Self {
            BoundCase {
                expression,
                statements,
            }
        }

        pub fn expression(&self) -> &BoundExpression {
            &self.expression
        }
        pub fn statements(&self) -> &Vec<BoundStatement> {
            &self.statements
        }
    }

    impl fmt::Display for BoundVariable {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "position: {}, data_type: {}",
                self.position, self.data_type
            )
        }
    }

    impl ops::Add<BoundLiteralValue> for BoundLiteralValue {
        type Output = BoundLiteralValue;

        fn add(self, rhs: BoundLiteralValue) -> Self::Output {
            match self {
                BoundLiteralValue::Pp(lpp) => match rhs {
                    BoundLiteralValue::Pp(rpp) => BoundLiteralValue::Pp(lpp + rpp),
                    _ => panic!("Undefined operation"),
                },
                _ => panic!("Undefined operation"),
            }
        }
    }

    impl ops::Sub for BoundLiteralValue {
        type Output = BoundLiteralValue;

        fn sub(self, rhs: Self) -> Self::Output {
            match self {
                BoundLiteralValue::Pp(lpp) => match rhs {
                    BoundLiteralValue::Pp(rpp) => BoundLiteralValue::Pp(lpp - rpp),
                    _ => panic!("Undefined operation"),
                },
                _ => panic!("Undefined operation"),
            }
        }
    }

    impl ops::Div for BoundLiteralValue {
        type Output = BoundLiteralValue;

        fn div(self, rhs: Self) -> Self::Output {
            match self {
                BoundLiteralValue::Pp(lpp) => match rhs {
                    BoundLiteralValue::Pp(rpp) => BoundLiteralValue::Pp(lpp / rpp),
                    _ => panic!("Undefined operation"),
                },
                _ => panic!("Undefined operation"),
            }
        }
    }

    impl ops::Mul for BoundLiteralValue {
        type Output = BoundLiteralValue;

        fn mul(self, rhs: Self) -> Self::Output {
            match self {
                BoundLiteralValue::Pp(lpp) => match rhs {
                    BoundLiteralValue::Pp(rpp) => BoundLiteralValue::Pp(lpp * rpp),
                    _ => panic!("Undefined operation"),
                },
                _ => panic!("Undefined operation"),
            }
        }
    }

    impl BoundStructField {
        pub fn new(
            modifiers: Vec<Modifier>,
            data_type: BoundDataType,
            ident: String,
            offset: usize,
        ) -> Self {
            Self {
                modifiers,
                data_type,
                ident,
                offset,
            }
        }

        pub fn has_modifier(&self, modifier: Modifier) -> bool {
            self.modifiers.contains(&modifier)
        }

        pub fn modifiers(&self) -> &Vec<Modifier> {
            &self.modifiers
        }
        pub fn data_type(&self) -> &BoundDataType {
            &self.data_type
        }
        pub fn ident(&self) -> &str {
            &self.ident
        }
        pub fn offset(&self) -> usize {
            self.offset
        }
    }
}

mod optimizer {}

mod emitter {
    use std::fmt;

    #[derive(Clone, Debug)]
    pub enum Instruction {
        /// Push the literal value arg onto the stack.
        Literal {
            value: i32,
        },
        /// Return from a subroutine. This instruction uses the stack frame (or block mark) from the current invocation of the subroutine to clear the stack of all data local to the current subroutine, restore the base register, and restore the program counter. Like all operations which require no arguments, it uses the op code OPR, with a second argument (here zero) indicating which of the zero-argument operations to perform.
        Operation {
            operation: OperationType,
        },
        /// Load (i.e. push onto the stack) the value of the cell identified by level and offset. A level value of 0 means the variable is in the currently executing procedure; 1 means it's in the immediately enclosing region of the program. 2 means it's the region outside that (in PL/0 as in Pascal procedures can nest indefinitely). The offset distinguishes among the variables declared at that level.
        Load {
            level: usize,
            offset: i32,
        },
        /// Store the value currently at the top of the stack to the memory cell identified by level and offset, popping the value off the stack in the process.
        Store {
            level: usize,
            offset: i32,
        },
        /// Call the subroutine at location address, which is level nesting levels different from the nesting level of the currently executing code. This instruction pushes a stack frame (or block mark) onto the stack, storing
        ///
        ///     the base address for variables, level blocks down on the stack (so that variables in outer blocks can be referred to and modified)
        ///     the current base address (so that it can be restored when the subroutine returns)
        ///     the current program counter (so that it can be restored when the subroutine returns)
        Call {
            level: usize,
            address: Address,
        },
        Return,
        Int {
            size: i32,
        },
        /// Jump to the instruction at address.
        Jump {
            address: Address,
        },
        /// Pop the current value from the top of the stack. If it's 0 (false), jump to the instruction at address. Otherwise, continue with the current location of the program counter.
        Jmc {
            address: Address,
        },
        // TODO: Those aren't instructions! Make a new enum.
        Dbg {
            debug_keyword: DebugKeyword,
        },
        Pld,
        Sta,
    }

    #[derive(Clone, Copy, Debug)]
    pub enum OperationType {
        Return = 0,
        /// Negate the value on the top of the stack (i.e. multiply by -1).
        Negate = 1,
        /// Add the two values at the top of the stack and replace them with their sum.
        Add = 2,
        /// Subtract the value at the top of the stack from the value below it; replace the diminuend and the subtrahend with their difference.
        Subtract = 3,
        /// Multiply the two values at the top of the stack and replace them with their product.
        Multiply = 4,
        /// Perform integer division on the two values at the top of the stack. The value on top of the stack becomes the divisor, the value below it the dividend. Replace the two values with their integer quotient.
        Divide = 5,
        Mod = 6,
        /// Test the value at the top of the stack to see if it's odd or not.
        Odd = 7,
        /// Test the two values at the top of the stack to see if they are equal or not.
        Equal = 8,
        /// Test the two values at the top of the stack to see if they are unequal or not.
        NotEqual = 9,
        /// Test the two values x and y at the top of the stack to see if x is less than y or not.
        LessThan = 10,
        /// Test the two values x and y at the top of the stack to see if x is greater than y or not.
        GreaterThanOrEqualTo = 11,
        /// Test the two values x and y at the top of the stack to see if x is greater than or equal to y, or not.
        GreaterThan = 12,
        /// Test the two values x and y at the top of the stack to see if x is less than or equal to y, or not.
        LessThanOrEqualTo = 13,
    }

    #[derive(Clone, Debug)]
    pub enum Address {
        Absolute(usize),
        Label(String),
    }

    #[derive(Clone, Debug)]
    pub enum DebugKeyword {
        Registers,
        Stack,
        StackA,
        StackRg { start: u32, end: u32 },
        StackN { amount: u32 },
        Echo { message: String },
    }

    impl fmt::Display for Instruction {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{self:?}")
        }
    }

    impl fmt::Display for Address {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Absolute(absolute_address) => write!(f, "{absolute_address}")?,
                Self::Label(label) => write!(f, "@{label}")?,
            };

            Ok(())
        }
    }
}

pub mod compiler {
    use std::io::Write;
    use std::{cell, error, fs, io, process, rc, time};

    use crate::parse::analysis::BoundTranslationUnit;
    use crate::parse::error_diagnosis::SyntaxError;
    use crate::parse::lexer::Token;
    use crate::parse::parser::TranslationUnit;
    use crate::parse::{Emitter, ErrorDiagnosis, Lexer, Optimizer, Parser, SemanticAnalyzer};

    pub struct DppCompiler;

    const OPTIMIZATION_COUNT: u32 = 2;
    impl DppCompiler {
        fn parse_args(bools: &[bool], params: &[&str]) -> Vec<String> {
            if bools.len() != params.len() {
                panic!("Invalid arguments");
            }

            if bools.len() != 6 {
                panic!("Invalid arguments");
            }

            let mut args = Vec::with_capacity(6);
            for i in 0..6 {
                args.push(format!("{}{}", if bools[i] { "+" } else { "-" }, params[i]));
            }

            args
        }

        pub fn compile_translation_unit(
            a_absolute_addressing: bool,
            l_print_program_with_absolute_addresses: bool,
            i_interpret_code: bool,
            t_debug_run_instructions: bool,
            s_debug_store_instructions: bool,
            d_debug_mode: bool,
            file_path: &str,
            output_file: &str,
            pl0_interpret_path: &str,
        ) -> Result<(), Box<dyn error::Error>> {
            let file_contents = fs::read_to_string(file_path)?;
            let error_diag = rc::Rc::new(cell::RefCell::new(ErrorDiagnosis::new(
                file_path,
                &file_contents,
            )));

            println!("Parsing program...");
            let start = time::Instant::now();
            {
                // Lex -> parse -> analyze -> optimize -> emit.
                let tokens = Self::lex(&file_contents, &error_diag)?;
                let translation_unit = Self::parse(tokens, &error_diag)?;
                let bound_translation_unit = Self::analyze(&translation_unit, &error_diag)?;
                println!("Optimizing {OPTIMIZATION_COUNT} times");
                let mut root_optimizer = Optimizer::new();
                let mut optimized_translation_unit = bound_translation_unit;
                for _ in 0..OPTIMIZATION_COUNT {
                    optimized_translation_unit =
                        root_optimizer.optimize(optimized_translation_unit);
                }
                println!("Printed optimizations into \"out/dpp/optimizations.txt\"");
                fs::write(
                    "out/dpp/optimizations.txt",
                    root_optimizer.optimizations.join("\n\n"),
                )?;
                Self::emit(output_file, optimized_translation_unit, &error_diag)?;
                error_diag.borrow_mut().check_errors()?;
            }
            let duration = start.elapsed();
            println!("Program parsed in {:?}", duration);

            println!("Running program...");
            let start = time::Instant::now();
            {
                let mut args = Self::parse_args(
                    &[
                        a_absolute_addressing,
                        l_print_program_with_absolute_addresses,
                        i_interpret_code,
                        t_debug_run_instructions,
                        s_debug_store_instructions,
                        d_debug_mode,
                    ],
                    &["a", "l", "i", "t", "s", "d"],
                );
                args.push(output_file.to_string());
                let child = process::Command::new(pl0_interpret_path)
                    .args(args)
                    .stdout(process::Stdio::piped())
                    .stderr(process::Stdio::piped())
                    .spawn()?;

                let out = child.wait_with_output()?;
                let stdout = String::from_utf8(out.stdout)?;
                let stderr = String::from_utf8(out.stderr)?;

                if l_print_program_with_absolute_addresses {
                    let mut file = fs::File::create(format!("{output_file}.absolute"))?;
                    let mut buf_writer = io::BufWriter::new(&mut file);
                    stdout
                        .lines()
                        .take_while(|&line| line != "START PL/0")
                        .for_each(|line| {
                            writeln!(buf_writer, "{}", line).unwrap();
                        });
                }

                println!("{stdout}");

                if !stderr.is_empty() {
                    eprintln!("ERROR: {stderr}");
                }
            }
            let duration = start.elapsed();
            println!("Program finished in {:?}", duration);

            Ok(())
        }

        fn lex<'a>(
            input: &'a str,
            error_diag: &rc::Rc<cell::RefCell<ErrorDiagnosis<'a, '_>>>,
        ) -> Result<Vec<Token<'a>>, SyntaxError> {
            Lexer::new(input, error_diag.clone()).lex()
        }

        fn parse<'a>(
            tokens: Vec<Token<'a>>,
            error_diag: &rc::Rc<cell::RefCell<ErrorDiagnosis<'a, '_>>>,
        ) -> Result<TranslationUnit<'a>, SyntaxError> {
            Parser::new(rc::Rc::new(tokens), error_diag.clone()).parse()
        }

        fn analyze<'a>(
            translation_unit: &'a TranslationUnit<'a>,
            error_diag: &rc::Rc<cell::RefCell<ErrorDiagnosis<'a, '_>>>,
        ) -> Result<BoundTranslationUnit, SyntaxError> {
            SemanticAnalyzer::new(rc::Rc::clone(error_diag)).analyze(translation_unit)
        }

        fn optimize<'a>(
            translation_unit: BoundTranslationUnit,
            optimization_count: u32,
            optimizer: &mut Optimizer,
        ) -> BoundTranslationUnit {
            if optimization_count == 0 {
                return translation_unit;
            }
            if optimization_count == 1 {
                return optimizer.optimize(translation_unit);
            }
            Self::optimize(translation_unit, optimization_count - 1, optimizer)
        }

        fn emit(
            output_file: &str,
            translation_unit: BoundTranslationUnit,
            error_diag: &rc::Rc<cell::RefCell<ErrorDiagnosis<'_, '_>>>,
        ) -> io::Result<()> {
            Emitter::new(rc::Rc::clone(error_diag)).emit_to_writer(
                &mut io::BufWriter::new(fs::File::create(output_file)?),
                translation_unit,
                true,
            )
        }
    }

    #[cfg(test)]
    mod lexer_tests {
        use std::cell;
        use std::rc;

        use itertools::Itertools;

        use TokenKind as TK;

        use crate::parse::lexer::{LiteralKind, TokenKind};
        use crate::parse::{ErrorDiagnosis, Lexer};

        fn test_generic_lex(
            input: &str,
            result_should_be_ok: bool,
            token_len: usize,
            expected_output: Vec<TokenKind>,
        ) {
            let error_diag = rc::Rc::new(cell::RefCell::new(ErrorDiagnosis::new("", input)));
            let lexer = Lexer::new(input, error_diag.clone());
            let result = lexer.lex();

            if !result_should_be_ok {
                assert!(result.is_err(), "Syntax error should be present.");
            } else {
                assert!(result.is_ok(), "No syntax error should be present.");
                let tokens = result.unwrap();
                assert_eq!(tokens.len(), token_len);

                let output = tokens.iter().map(|token| token.kind()).collect_vec();
                assert_eq!(output, expected_output);
            }
        }

        #[test]
        fn test() {
            test_generic_lex(
                "pp -> x = 0;",
                true,
                7,
                vec![
                    TK::PpKeyword,
                    TK::Arrow,
                    TK::Identifier,
                    TK::Equal,
                    TK::Literal(LiteralKind::Pp),
                    TK::Semicolon,
                    TK::Eof,
                ],
            );
            test_generic_lex("dsa ó", false, 0, vec![]);
        }
    }

    #[cfg(test)]
    mod generic_tests {}
}
