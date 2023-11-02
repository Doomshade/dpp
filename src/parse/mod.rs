use std::io::Write;
use std::{cell, collections, fs, io, rc};

use dpp_macros::Pos;

use crate::parse::analysis::{BoundTranslationUnit, BoundVariablePosition, SymbolTable};
use crate::parse::emitter::{Address, DebugKeyword, Instruction, OperationType};
use crate::parse::error_diagnosis::ErrorMessage;
use crate::parse::lexer::{Token, TokenKind};
use crate::parse::parser::{Block, DataType, Expression, Function, Variable};

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
    loop_stack: usize,
    assignment_count: collections::HashMap<BoundVariablePosition, usize>,
    referenced_variables: collections::HashSet<BoundVariablePosition>,
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
}

#[derive(Debug)]
pub struct Optimizer {
    optimizations: Vec<String>,
    referenced_variables: collections::HashSet<BoundVariablePosition>,
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

    fn matches_token_kind(&mut self, token_kind: TokenKind) -> bool {
        if let Some(token) = self.token() {
            return token.kind() == token_kind;
        }
        false
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
                TokenKind::XxlppKeyword
                    | TokenKind::PpKeyword
                    | TokenKind::SppKeyword
                    | TokenKind::XsppKeyword
                    | TokenKind::PKeyword
                    | TokenKind::NoppKeyword
                    | TokenKind::BoobaKeyword
                    | TokenKind::YarnKeyword
            );
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
}

impl<'a, 'b> SemanticAnalyzer<'a, 'b> {
    pub fn new(error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>) -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            error_diag,
            loop_stack: 0,
            assignment_count: collections::HashMap::new(),
            referenced_variables: collections::HashSet::new(),
        }
    }

    fn symbol_table_mut(&mut self) -> &mut SymbolTable<'a> {
        &mut self.symbol_table
    }

    fn symbol_table(&self) -> &SymbolTable<'a> {
        &self.symbol_table
    }

    fn check_if_mixed_data_types(
        &self,
        expected_data_type: &DataType<'a>,
        got: &DataType<'a>,
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
        expected_data_type: &DataType<'a>,
        got: Option<&DataType<'a>>,
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

    fn increment_assignment_at(&mut self, position: BoundVariablePosition) {
        let value = self.assignment_count.get(&position).unwrap_or(&0);
        self.assignment_count.insert(position, value + 1);
    }

    fn begin_function(&mut self, function: &Function<'a>) {
        self.loop_stack = 0;
        let ref_mut = self.symbol_table_mut();
        ref_mut.push_function(function.clone());
        ref_mut.push_scope();
        function
            .parameters()
            .iter()
            .for_each(|parameter| ref_mut.push_local_variable(parameter, true));
    }

    fn end_function(&mut self) {
        self.symbol_table_mut().pop_scope();
    }
}

impl Optimizer {
    pub fn optimize(&mut self, translation_unit: BoundTranslationUnit) -> BoundTranslationUnit {
        self.optimize_translation_unit(translation_unit)
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
                    if compiler::DEBUG {
                        pc -= 1;
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
                .expect(format!("Did not emit {label}").as_str()),
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

    fn load_variable(&mut self, position: &BoundVariablePosition) {
        self.load(position.level(), position.offset());
    }

    fn load(&mut self, level: usize, offset: i32) {
        self.emit_instruction(Instruction::Load { level, offset });
    }

    fn store_variable(&mut self, position: &BoundVariablePosition) {
        self.store(position.level(), position.offset());
    }

    fn store(&mut self, level: usize, offset: i32) {
        self.emit_instruction(Instruction::Store { level, offset });
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
        if compiler::DEBUG {
            self.emit_instruction(Instruction::Dbg { debug_keyword });
        }
    }

    fn emit_call(&mut self, level: usize, address: Address) {
        self.emit_instruction(Instruction::Call { level, address });
    }

    fn emit_literal(&mut self, value: i32) {
        self.emit_instruction(Instruction::Literal { value })
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

    use dpp_macros::Pos;
    use dpp_macros_derive::Pos;

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
        Identifier,         // identifier literal
        NumberLiteral,      // number literal
        PLiteral,           // char literal
        YarnLiteral,        // String literal
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
        Comma,              // ,
        IfKeyword,          // if
        LetKeyword,         // let
        ByeKeyword,         // return
        FUNcKeyword,        // function
        PprintKeyword,      // write()
        PprintlnKeyword,    // writeln()
        PpanicKeyword,      // panic()
        PpinKeyword,        // read()
        XxlppKeyword,       // i64
        PpKeyword,          // i32
        SppKeyword,         // i16
        XsppKeyword,        // i8
        PKeyword,           // char
        BoobaKeyword,       // bool
        NoppKeyword,        // void
        YarnKeyword,        // String
        RatioKeyword,       // ratio
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
        PipePipe,           // ||
        AmpersandAmpersand, // &&
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
                Self::NumberLiteral => "integer",
                Self::PLiteral => "p",
                Self::YarnLiteral => "yarn",
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
                Self::LetKeyword => "\"let\"",
                Self::ByeKeyword => "\"bye\"",
                Self::PprintKeyword => "\"pprint\"",
                Self::PprintlnKeyword => "\"pprintln\"",
                Self::PpanicKeyword => "\"ppanic\"",
                Self::PpinKeyword => "\"ppin\"",
                Self::FUNcKeyword => "\"FUNc\"",
                Self::ElseKeyword => "\"else\"",
                Self::ForKeyword => "\"for\"",
                Self::XxlppKeyword => "data type \"xxlpp\"",
                Self::PpKeyword => "data type \"pp\"",
                Self::SppKeyword => "data type \"spp\"",
                Self::XsppKeyword => "data type \"xspp\"",
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
                Self::CaseKeyword => "\"case\"",
                Self::RatioKeyword => "\"ratio\"",
            };
            write!(f, "{text_representation}")
        }
    }
}

mod parser {
    use std::fmt;
    use std::mem;

    use dpp_macros::Pos;
    use dpp_macros_derive::Pos;

    #[derive(Clone, Debug, Pos)]
    pub struct TranslationUnit<'a> {
        position: (u32, u32),
        functions: Vec<Function<'a>>,
        global_statements: Vec<Statement<'a>>,
    }

    #[derive(Clone, Debug, Pos)]
    pub struct Function<'a> {
        position: (u32, u32),
        identifier: &'a str,
        return_type: DataType<'a>,
        parameters: Vec<Variable<'a>>,
        block: Block<'a>,
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
            expression: Expression<'a>,
        },
    }

    #[derive(Clone, Debug, Pos)]
    pub struct Variable<'a> {
        position: (u32, u32),
        identifier: &'a str,
        data_type: DataType<'a>,
        size: usize,
        value: Option<Expression<'a>>,
    }

    #[derive(Clone, Debug, Pos)]
    pub struct Case<'a> {
        position: (u32, u32),
        expression: Expression<'a>,
        block: Box<Block<'a>>,
    }

    #[derive(Debug, Clone)]
    pub enum DataType<'a> {
        // Xxlpp, Pp, Spp, Xspp
        Number(NumberType),
        // char
        P,
        // string
        Yarn,
        // bool
        Booba,
        // void
        Nopp,
        // ratio
        Ratio,
        Struct { name: &'a str },
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum NumberType {
        Pp,    // int
        Ratio, // ratio
        Glide, // float
    }

    #[derive(Clone, Debug)]
    pub struct Struct {}

    #[derive(Clone, Debug, Pos)]
    pub enum Expression<'a> {
        // TODO: Use LiteralExpression instead.
        Number {
            position: (u32, u32),
            number_type: NumberType,
            value: i32,
        },
        P {
            position: (u32, u32),
            value: char,
        },
        Booba {
            position: (u32, u32),
            value: bool,
        },
        Yarn {
            position: (u32, u32),
            value: &'a str,
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
        Invalid {
            position: (u32, u32),
        },
    }

    #[derive(Clone, PartialEq, Debug)]
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

    #[derive(Clone, PartialEq, Debug)]
    pub enum UnaryOperator {
        Not,
        Negate,
    }

    impl<'a> TranslationUnit<'a> {
        pub fn new(functions: Vec<Function<'a>>, global_statements: Vec<Statement<'a>>) -> Self {
            TranslationUnit {
                position: (1, 1),
                functions,
                global_statements,
            }
        }

        pub fn functions(&self) -> &Vec<Function<'a>> {
            &self.functions
        }
        pub fn global_statements(&self) -> &Vec<Statement<'a>> {
            &self.global_statements
        }
    }

    impl<'a> Function<'a> {
        pub fn new(
            position: (u32, u32),
            identifier: &'a str,
            return_type: DataType<'a>,
            parameters: Vec<Variable<'a>>,
            block: Block<'a>,
        ) -> Self {
            Function {
                position,
                identifier,
                return_type,
                parameters,
                block,
            }
        }

        pub fn identifier(&self) -> &'a str {
            self.identifier
        }
        pub fn return_type(&self) -> &DataType<'a> {
            &self.return_type
        }
        pub fn block(&self) -> &Block<'a> {
            &self.block
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
            data_type: DataType<'a>,
            value: Option<Expression<'a>>,
        ) -> Self {
            Variable {
                position,
                identifier,
                size: data_type.size(),
                data_type,
                value,
            }
        }

        pub fn position(&self) -> (u32, u32) {
            self.position
        }
        pub fn identifier(&self) -> &'a str {
            self.identifier
        }
        pub fn data_type(&self) -> &DataType<'a> {
            &self.data_type
        }
        pub fn size(&self) -> usize {
            self.size
        }
        pub fn value(&self) -> Option<&Expression<'a>> {
            self.value.as_ref()
        }
        pub fn size_in_instructions(&self) -> usize {
            ((self.size() - 1) / 4) + 1
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

    impl<'a> DataType<'a> {
        pub fn size(&self) -> usize {
            match self {
                DataType::Number(number) => match number {
                    NumberType::Pp => mem::size_of::<i32>(),
                    NumberType::Ratio => mem::size_of::<i32>() * 2,
                    NumberType::Glide => mem::size_of::<i32>() * 2,
                },
                DataType::P => mem::size_of::<char>(),
                DataType::Booba => mem::size_of::<bool>(),
                DataType::Nopp => 0,
                _ => panic!("Invalid data type {self}"),
            }
        }

        pub fn size_in_instructions(&self) -> usize {
            let size = self.size();
            if size == 0 {
                return 0;
            }
            return ((size - 1) / 4) + 1;
        }
    }

    // impl PosMacro for Statement<'_> {
    //     fn row(&self) -> u32 {
    //         match self {
    //             Statement::VariableDeclaration { position, .. } => position.0,
    //             Statement::If { position, .. } => position.0,
    //             Statement::IfElse { position, .. } => position.0,
    //             Statement::Bye { position, .. } => position.0,
    //             Statement::Print { position, .. } => position.0,
    //             Statement::Block { position, .. } => position.0,
    //             Statement::Expression { position, .. } => position.0,
    //             Statement::Empty { position, .. } => position.0,
    //             Statement::For { position, .. } => position.0,
    //             Statement::While { position, .. } => position.0,
    //             Statement::DoWhile { position, .. } => position.0,
    //             Statement::Loop { position, .. } => position.0,
    //             Statement::Break { position, .. } => position.0,
    //             Statement::Continue { position, .. } => position.0,
    //             Statement::Switch { position, .. } => position.0,
    //             Statement::Assignment { position, .. } => position.0,
    //         }
    //     }
    //
    //     fn col(&self) -> u32 {
    //         match self {
    //             Statement::VariableDeclaration { position, .. } => position.1,
    //             Statement::If { position, .. } => position.1,
    //             Statement::IfElse { position, .. } => position.1,
    //             Statement::Bye { position, .. } => position.1,
    //             Statement::Print { position, .. } => position.1,
    //             Statement::Block { position, .. } => position.1,
    //             Statement::Expression { position, .. } => position.1,
    //             Statement::Empty { position, .. } => position.1,
    //             Statement::For { position, .. } => position.1,
    //             Statement::While { position, .. } => position.1,
    //             Statement::DoWhile { position, .. } => position.1,
    //             Statement::Loop { position, .. } => position.1,
    //             Statement::Break { position, .. } => position.1,
    //             Statement::Continue { position, .. } => position.1,
    //             Statement::Switch { position, .. } => position.1,
    //             Statement::Assignment { position, .. } => position.1,
    //         }
    //     }
    // }

    impl fmt::Display for Expression<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let formatted = match self {
                Expression::Number { value, .. } => value.to_string(),
                Expression::P { value, .. } => value.to_string(),
                Expression::Booba { value, .. } => value.to_string(),
                Expression::Yarn { value, .. } => value.to_string(),
                Expression::Unary { operand, op, .. } => {
                    format!("Unary expression {}{}", op, operand)
                }
                Expression::Binary { .. } => "Binary expression".to_string(),
                Expression::Identifier { identifier, .. } => identifier.to_string(),
                Expression::FunctionCall { identifier, .. } => {
                    format!("Function {}", identifier)
                }
                Expression::Invalid { .. } => "Invalid expression".to_string(),
            };
            write!(f, "{}", formatted)?;
            Ok(())
        }
    }

    impl PartialEq for DataType<'_> {
        fn eq(&self, other: &Self) -> bool {
            matches!(
                (self, other),
                (DataType::Number(..), DataType::Number(..))
                    | (DataType::P, DataType::P)
                    | (DataType::Yarn, DataType::Yarn)
                    | (DataType::Booba, DataType::Booba)
                    | (DataType::Nopp, DataType::Nopp)
            )
        }
    }

    impl fmt::Display for DataType<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                DataType::Number(_) => write!(f, "number")?,
                DataType::P => write!(f, "p")?,
                DataType::Yarn => write!(f, "yarn")?,
                DataType::Booba => write!(f, "booba")?,
                DataType::Nopp => write!(f, "nopp")?,
                DataType::Ratio => write!(f, "ratio")?,
                DataType::Struct { name } => write!(f, "struct {name}")?,
            };

            Ok(())
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
    use std::{collections, fmt};

    use crate::parse::parser::{
        BinaryOperator, DataType, Expression, Function, NumberType, UnaryOperator, Variable,
    };

    #[derive(Debug)]
    pub struct SymbolTable<'a> {
        /// The global scope holding global variables and function identifiers.
        global_scope: GlobalScope<'a>,
        /// Current stack of function scopes.
        function_scopes: Vec<FunctionScope<'a>>,
    }

    #[derive(Clone, Debug, Default)]
    pub struct Scope<'a> {
        /// Variable symbol table.
        variables: collections::HashMap<&'a str, VariableDescriptor<'a>>,
        /// Function symbol table.
        functions: collections::HashMap<&'a str, FunctionDescriptor<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct GlobalScope<'a> {
        scope: Scope<'a>,
        stack_position: usize,
    }

    #[derive(Clone, Debug)]
    pub struct FunctionScope<'a> {
        // This is a stack of scopes that is popped once the scope is ended.
        scopes: Vec<Scope<'a>>,
        /// The identifier of this function scope (i.e. the function identifier).
        function_identifier: &'a str,
        /// The stack position.
        stack_position: usize,
    }

    #[derive(Clone, Debug)]
    pub struct VariableDescriptor<'a> {
        stack_position: usize,
        data_type: DataType<'a>,
        size: usize,
        value: Option<Expression<'a>>,
        is_parameter: bool,
        initialized: bool,
    }

    #[derive(Clone, Debug)]
    pub struct FunctionDescriptor<'a> {
        return_type: DataType<'a>,
        parameters: Vec<Variable<'a>>,
        function_id: usize,
    }

    #[derive(Clone, Debug)]
    pub struct BoundTranslationUnit {
        pub functions: Vec<BoundFunction>,
        main_function_identifier: usize,
        global_stack_frame_size: usize,
        pub global_variable_assignments: Vec<BoundVariableAssignment>,
    }

    #[derive(Clone, Debug)]
    pub struct BoundFunction {
        identifier: usize,
        is_main_function: bool,
        stack_frame_size: usize,
        return_size: usize,
        parameters: Vec<BoundVariablePosition>,
        pub statements: Vec<BoundStatement>,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub struct BoundVariableAssignment {
        pub position: BoundVariablePosition,
        pub value: BoundExpression,
    }

    #[derive(Clone, PartialEq, Debug)]
    pub enum BoundExpression {
        Number {
            number_type: NumberType,
            value: i32,
        },
        P(char),
        Booba(bool),
        Yarn(String),
        Unary {
            op: UnaryOperator,
            operand: Box<BoundExpression>,
        },
        Binary {
            lhs: Box<BoundExpression>,
            op: BinaryOperator,
            rhs: Box<BoundExpression>,
        },
        Variable(BoundVariablePosition),
        FunctionCall {
            level: usize,
            identifier: usize,
            return_type_size: usize,
            arguments_size: usize,
            arguments: Vec<BoundExpression>,
        },
    }

    #[derive(Eq, PartialEq, Hash, Clone, Debug)]
    pub struct BoundVariablePosition {
        level: usize,
        offset: i32,
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
            return_offset: i32,
        },
        Print {
            print_function: fn(&str),
            expression: BoundExpression,
        },
        Expression(BoundExpression),
        For {
            ident_position: BoundVariablePosition,
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
        expression: BoundExpression,
        statements: Vec<BoundStatement>,
    }

    impl<'a> SymbolTable<'a> {
        pub fn new() -> Self {
            SymbolTable {
                global_scope: GlobalScope::new(),
                function_scopes: Vec::new(),
            }
        }

        pub fn set_variable_initialized(&mut self, identifier: &str) {
            let (_, variable_descriptor) = self.variable_mut(identifier);
            if let Some(variable_descriptor) = variable_descriptor {
                variable_descriptor.set_initialized();
            }
        }

        pub fn current_function_scope(&self) -> Option<&FunctionScope<'a>> {
            self.function_scopes.last()
        }

        pub fn push_global_variable(&mut self, variable: &Variable<'a>) {
            self.global_scope.push_variable(variable);
        }

        pub fn push_local_variable(&mut self, variable: &Variable<'a>, is_parameter: bool) {
            self.current_function_scope_mut()
                .expect("A function scope")
                .push_variable(variable, is_parameter);
        }

        pub fn has_global_function(&self, identifier: &str) -> bool {
            self.global_scope.has_function(identifier)
        }

        pub fn push_global_function(&mut self, function: &Function<'a>) {
            let function_id = self.global_scope.scope.functions.len();
            self.global_scope.push_function(function, function_id);
            assert!(self.global_scope.scope.functions.len() > function_id);
        }

        fn push_function_scope(&mut self, function_identifier: &'a str) {
            self.function_scopes
                .push(FunctionScope::new(function_identifier))
        }

        pub fn function(&self, identifier: &str) -> Option<&FunctionDescriptor<'a>> {
            self.global_scope.get_function_descriptor(identifier)
        }

        pub fn push_scope(&mut self) {
            self.current_function_scope_mut()
                .expect("To be inside function scope")
                .push_scope();
        }

        pub fn pop_scope(&mut self) {
            self.current_function_scope_mut()
                .expect("To be inside function scope")
                .pop_scope();
        }

        fn variable_mut(
            &mut self,
            identifier: &str,
        ) -> (usize, Option<&mut VariableDescriptor<'a>>) {
            // If we aren't in a function scope we are in the global scope
            // -> the global variable is in level 0.
            if self.current_function_scope().is_none() {
                return (0, self.global_scope.get_variable_descriptor_mut(identifier));
            }

            // If we are in function scope we need to check if the variable
            // is a local variable or a global variable.
            // TODO: This is utterly retarded. We have to lookup the variable TWICE because
            // the borrow checker is an asshole.
            if self.local_variable(identifier).is_some() {
                return (0, self.local_variable_mut(identifier));
            }
            (1, self.global_variable_mut(identifier))
        }

        pub fn variable(&self, identifier: &str) -> (usize, Option<&VariableDescriptor<'a>>) {
            // If we aren't in a function scope we are in the global scope
            // -> the global variable is in level 0.
            if self.current_function_scope().is_none() {
                return (0, self.global_scope.get_variable_descriptor(identifier));
            }

            // If we are in function scope we need to check if the variable
            // is a local variable or a global variable.

            // Check for local variable first.
            if let Some(local_variable) = self.local_variable(identifier) {
                return (0, Some(local_variable));
            }

            // Then global variable.
            (1, self.global_variable(identifier))
        }

        pub fn push_function(&mut self, function: Function<'a>) {
            self.push_function_scope(function.identifier());
        }

        pub fn global_variable(&self, identifier: &str) -> Option<&VariableDescriptor<'a>> {
            self.global_scope.get_variable_descriptor(identifier)
        }

        pub fn global_variable_mut(
            &mut self,
            identifier: &str,
        ) -> Option<&mut VariableDescriptor<'a>> {
            self.global_scope.get_variable_descriptor_mut(identifier)
        }

        pub fn local_variable(&self, identifier: &str) -> Option<&VariableDescriptor<'a>> {
            self.current_function_scope()?.variable(identifier)
        }

        pub fn local_variable_mut(
            &mut self,
            identifier: &str,
        ) -> Option<&mut VariableDescriptor<'a>> {
            self.current_function_scope_mut()?.variable_mut(identifier)
        }

        // TODO: This could be done in O(1) but w/e.
        pub fn function_scope(&self, function_identifier: &str) -> Option<&FunctionScope<'a>> {
            self.function_scopes
                .iter()
                .find(move |func| func.function_identifier == function_identifier)
        }

        fn current_function_scope_mut(&mut self) -> Option<&mut FunctionScope<'a>> {
            self.function_scopes.last_mut()
        }
        pub fn global_scope(&self) -> &GlobalScope<'a> {
            &self.global_scope
        }
    }

    impl<'a> Scope<'a> {
        pub const ACTIVATION_RECORD_SIZE: usize = 3;

        fn push_variable_descriptor(
            &mut self,
            identifier: &'a str,
            variable_descriptor: VariableDescriptor<'a>,
        ) {
            self.variables.insert(identifier, variable_descriptor);
        }

        pub fn get_variable_descriptor(&self, identifier: &str) -> Option<&VariableDescriptor<'a>> {
            if let Some(variable) = self.variables.get(identifier) {
                return Some(variable);
            }
            None
        }

        pub fn get_variable_descriptor_mut(
            &mut self,
            identifier: &str,
        ) -> Option<&mut VariableDescriptor<'a>> {
            if let Some(variable) = self.variables.get_mut(identifier) {
                return Some(variable);
            }
            None
        }

        pub fn last_variable_descriptor(&self) -> Option<&VariableDescriptor<'a>> {
            self.variables.values().last()
        }

        fn push_function_descriptor(
            &mut self,
            identifier: &'a str,
            function_descriptor: FunctionDescriptor<'a>,
        ) {
            self.functions.insert(identifier, function_descriptor);
        }

        pub fn get_function_descriptor(&self, identifier: &str) -> Option<&FunctionDescriptor<'a>> {
            self.functions.get(identifier)
        }

        pub fn has_function(&self, identifier: &str) -> bool {
            self.functions.contains_key(identifier)
        }
    }

    impl<'a> GlobalScope<'a> {
        pub fn new() -> Self {
            // TODO: Need to offset this because we need the first
            // thing on the stack to be "1" because we call
            // main and then it fucking has to read the first thing
            // on the stack.
            GlobalScope {
                scope: Scope::default(),
                stack_position: Scope::ACTIVATION_RECORD_SIZE,
            }
        }

        pub fn push_variable(&mut self, variable: &Variable<'a>) {
            let variable_descriptor = VariableDescriptor::new(variable, self.stack_position, false);
            self.stack_position += variable_descriptor.size_in_instructions();
            self.scope
                .push_variable_descriptor(variable.identifier(), variable_descriptor);
        }

        pub fn get_variable_descriptor(&self, identifier: &str) -> Option<&VariableDescriptor<'a>> {
            self.scope.get_variable_descriptor(identifier)
        }

        pub fn get_variable_descriptor_mut(
            &mut self,
            identifier: &str,
        ) -> Option<&mut VariableDescriptor<'a>> {
            self.scope.get_variable_descriptor_mut(identifier)
        }

        pub fn push_function(&mut self, function: &Function<'a>, function_id: usize) {
            let function_descriptor = FunctionDescriptor::new(function, function_id);
            self.scope
                .push_function_descriptor(function.identifier(), function_descriptor);
        }

        pub fn get_function_descriptor(&self, identifier: &str) -> Option<&FunctionDescriptor<'a>> {
            self.scope.get_function_descriptor(identifier)
        }

        pub fn has_function(&self, identifier: &str) -> bool {
            self.scope.has_function(identifier)
        }
        pub fn stack_position(&self) -> usize {
            self.stack_position
        }
    }

    impl<'a> FunctionScope<'a> {
        pub fn new(function_identifier: &'a str) -> Self {
            FunctionScope {
                scopes: Vec::new(),
                function_identifier,
                stack_position: Scope::ACTIVATION_RECORD_SIZE,
            }
        }

        pub fn variable(&self, identifier: &str) -> Option<&VariableDescriptor<'a>> {
            for scope in self.scopes.iter().rev() {
                if let Some(variable) = scope.get_variable_descriptor(identifier) {
                    return Some(variable);
                }
            }
            None
        }

        pub fn variable_mut(&mut self, identifier: &str) -> Option<&mut VariableDescriptor<'a>> {
            for scope in self.scopes.iter_mut().rev() {
                if let Some(variable) = scope.get_variable_descriptor_mut(identifier) {
                    return Some(variable);
                }
            }
            None
        }

        pub fn function_identifier(&self) -> &'a str {
            self.function_identifier
        }

        pub fn push_variable(&mut self, variable: &Variable<'a>, is_parameter: bool) {
            let variable_descriptor =
                VariableDescriptor::new(variable, self.stack_position, is_parameter);
            self.stack_position += variable_descriptor.size_in_instructions();
            self.current_scope_mut()
                .expect("A scope")
                .push_variable_descriptor(variable.identifier(), variable_descriptor);
        }

        pub fn push_scope(&mut self) {
            self.scopes.push(Scope::default());
        }

        pub fn current_scope(&self) -> Option<&Scope<'a>> {
            self.scopes.last()
        }

        fn current_scope_mut(&mut self) -> Option<&mut Scope<'a>> {
            self.scopes.last_mut()
        }

        pub fn pop_scope(&mut self) {
            self.scopes.pop();
        }
        pub fn stack_position(&self) -> usize {
            self.stack_position
        }
    }

    impl<'a> VariableDescriptor<'a> {
        pub fn new(variable: &Variable<'a>, stack_position: usize, is_parameter: bool) -> Self {
            VariableDescriptor {
                stack_position,
                is_parameter,
                size: variable.size(),
                data_type: variable.data_type().clone(),
                value: variable.value().cloned(),
                initialized: false,
            }
        }

        pub fn size_in_instructions(&self) -> usize {
            ((self.size() - 1) / 4) + 1
        }

        pub fn set_initialized(&mut self) {
            self.initialized = true;
        }

        pub fn is_initialized(&self) -> bool {
            self.initialized || self.is_parameter || self.value.is_some()
        }

        pub fn stack_position(&self) -> usize {
            self.stack_position
        }
        pub fn data_type(&self) -> &DataType<'a> {
            &self.data_type
        }
        pub fn size(&self) -> usize {
            self.size
        }
    }

    impl<'a> FunctionDescriptor<'a> {
        pub fn new(function: &Function<'a>, function_id: usize) -> Self {
            FunctionDescriptor {
                return_type: function.return_type().clone(),
                parameters: function.parameters().clone(),
                function_id,
            }
        }

        pub fn return_type(&self) -> &DataType<'a> {
            &self.return_type
        }
        pub fn parameters(&self) -> &Vec<Variable<'a>> {
            &self.parameters
        }

        /// The size of parameters in instructions.
        pub fn parameters_size(&self) -> usize {
            self.parameters().iter().fold(0, |acc, parameter| {
                acc + parameter.data_type().size_in_instructions()
            })
        }
        pub fn function_id(&self) -> usize {
            self.function_id
        }
    }

    impl BoundTranslationUnit {
        pub fn new(
            functions: Vec<BoundFunction>,
            main_function_identifier: usize,
            global_stack_frame_size: usize,
            global_variable_assignments: Vec<BoundVariableAssignment>,
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
        pub fn global_variable_assignments(&self) -> &Vec<BoundVariableAssignment> {
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
            parameters: Vec<BoundVariablePosition>,
            statements: Vec<BoundStatement>,
        ) -> Self {
            BoundFunction {
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
        pub fn parameters(&self) -> &Vec<BoundVariablePosition> {
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
        pub fn new(position: BoundVariablePosition, value: BoundExpression) -> Self {
            BoundVariableAssignment { position, value }
        }
        pub fn position(&self) -> &BoundVariablePosition {
            &self.position
        }
        pub fn value(&self) -> &BoundExpression {
            &self.value
        }
    }

    impl BoundVariablePosition {
        pub fn new(level: usize, offset: i32) -> Self {
            BoundVariablePosition { level, offset }
        }

        pub fn level(&self) -> usize {
            self.level
        }
        pub fn offset(&self) -> i32 {
            self.offset
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

    impl fmt::Display for BoundVariablePosition {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{} {}", self.level, self.offset)
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
    use std::collections::HashSet;
    use std::io::Write;
    use std::{cell, error, fs, io, process, rc, time};

    use crate::parse::analysis::BoundTranslationUnit;
    use crate::parse::error_diagnosis::SyntaxError;
    use crate::parse::lexer::Token;
    use crate::parse::parser::TranslationUnit;
    use crate::parse::{Emitter, ErrorDiagnosis, Lexer, Optimizer, Parser, SemanticAnalyzer};

    pub struct DppCompiler;

    pub const DEBUG: bool = false;

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
                // Lex -> parse -> analyze -> emit.
                let tokens = Self::lex(&file_contents, &error_diag)?;
                let translation_unit = Self::parse(tokens, &error_diag)?;
                let bound_translation_unit = Self::analyze(&translation_unit, &error_diag)?;
                let mut optimizer = Optimizer {
                    optimizations: Vec::new(),
                    referenced_variables: HashSet::new(),
                };
                let optimized_translation_unit = optimizer.optimize(bound_translation_unit);
                fs::write(
                    "out/dpp/optimizations.txt",
                    optimizer.optimizations.join("\n"),
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
            translation_unit: &TranslationUnit<'a>,
            error_diag: &rc::Rc<cell::RefCell<ErrorDiagnosis<'a, '_>>>,
        ) -> Result<BoundTranslationUnit, SyntaxError> {
            SemanticAnalyzer::new(rc::Rc::clone(&error_diag)).analyze(&translation_unit)
        }

        fn emit<'a>(
            output_file: &str,
            translation_unit: BoundTranslationUnit,
            error_diag: &rc::Rc<cell::RefCell<ErrorDiagnosis<'a, '_>>>,
        ) -> io::Result<()> {
            Emitter::new(rc::Rc::clone(&error_diag)).emit_to_writer(
                &mut io::BufWriter::new(fs::File::create(output_file)?),
                translation_unit,
            )
        }
    }

    #[cfg(test)]
    mod lexer_tests {
        use std::cell;
        use std::rc;

        use TokenKind as TK;

        use crate::parse::lexer::TokenKind;
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

                let output = tokens
                    .iter()
                    .map(|token| token.kind())
                    .collect::<Vec<TokenKind>>();
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
                    TK::NumberLiteral,
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
