use std::cell;
use std::collections;
use std::rc;

use crate::parse::analysis::SymbolTable;
use crate::parse::emitter::Instruction;
use crate::parse::error_diagnosis::ErrorMessage;
use crate::parse::lexer::{Token, TokenKind};
use crate::parse::parser::{Block, DataType, Expression, Function, Variable};

pub mod analysis_impl;
pub mod emitter_impl;
pub mod error_diagnosis_impl;
pub mod lexer_impl;
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
    /// The input as a vector of characters because we want to index into it.
    chars: Vec<char>,
    /// The cursor to the chars vector.
    cursor: usize,
    row: u32,
    col: u32,
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
}

#[derive(Debug)]
pub struct Parser<'a, 'b> {
    tokens: rc::Rc<Vec<Token<'a>>>,
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
    curr_token_index: usize,
    position: (u32, u32),
    error: bool,
    fixing_parsing: bool,
}

#[derive(Debug)]
pub struct SemanticAnalyzer<'a, 'b> {
    symbol_table: SymbolTable<'a>,
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
    current_function: Option<&'a str>,
    loop_stack: usize,
}

#[derive(Debug)]
pub struct Emitter<'a, 'b> {
    error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
    /// The instructions to be emitted.
    code: Vec<Instruction>,
    /// Stack of function scopes. Each scope is pushed and popped when entering and exiting a function.
    symbol_table: rc::Rc<SymbolTable<'a>>,
    /// The labels of the program.
    labels: collections::HashMap<String, u32>,
    current_function: Option<&'a str>,
    function_scope_depth: collections::HashMap<&'a str, u32>,
    control_statement_count: u32,
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
            row: 1,
            col: 1,
            error_diag,
        }
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
        if advanced_bytes > 1 {
            println!("YO");
        }
        self.col += 1;
        self.cursor += 1;
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
            current_function: None,
            loop_stack: 0,
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
        got: &DataType<'a>,
        position: (u32, u32),
    ) {
        if expected_data_type != got {
            self.error_diag
                .borrow_mut()
                .invalid_data_type(position, expected_data_type, got)
        }
    }

    fn begin_function(&mut self, function: &Function<'a>) {
        self.loop_stack = 0;
        self.current_function = Some(function.identifier());
        let ref_mut = self.symbol_table_mut();
        ref_mut.push_function(function.clone());
        ref_mut.push_scope();
        function
            .parameters()
            .iter()
            .for_each(|parameter| ref_mut.push_local_variable(parameter.clone()));
    }

    fn end_function(&mut self) {
        self.current_function = None;
        self.symbol_table_mut().pop_scope();
    }
}

impl<'a, 'b> Emitter<'a, 'b> {
    pub fn new(
        symbol_table: rc::Rc<SymbolTable<'a>>,
        error_diag: rc::Rc<cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
    ) -> Self {
        Self {
            error_diag,
            code: Vec::new(),
            labels: collections::HashMap::new(),
            control_statement_count: 0,
            symbol_table,
            function_scope_depth: collections::HashMap::new(),
            current_function: None,
        }
    }

    fn symbol_table(&self) -> &rc::Rc<SymbolTable<'a>> {
        &self.symbol_table
    }
}

mod error_diagnosis {
    use std::cmp;
    use std::error;
    use std::fmt;

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
        Identifier,
        Number,
        P,
        Yarn,
        BangEqual,
        Comment,
        Whitespace,
        Eof,
        Unknown,
        EqualEqual,
        Equal,
        Bang,
        Star,
        ForwardSlash,
        BackSlash,
        Plus,
        MinusEqual,
        PlusEqual,
        PlusDash,
        Dash,
        Greater,
        GreaterEqual,
        Less,
        LessEqual,
        NomKeyword,
        YemKeyword,
        OpenParen,
        CloseParen,
        OpenBrace,
        CloseBrace,
        OpenBracket,
        CloseBracket,
        Colon,
        Semicolon,
        Ampersand,
        Pipe,
        Comma,
        IfKeyword,
        // if
        LetKeyword,
        // let
        ByeKeyword,
        // return
        FUNcKeyword,
        // function
        PprintKeyword,
        // write()
        PprintlnKeyword,
        // writeln()
        PpanicKeyword,
        // panic()
        PpinKeyword,
        // read()
        XxlppKeyword,
        // i64
        PpKeyword,
        // i32
        SppKeyword,
        // i16
        XsppKeyword,
        // i8
        PKeyword,
        // char
        BoobaKeyword,
        // bool
        NoppKeyword,
        // void
        YarnKeyword,
        // String
        ForKeyword,
        ElseKeyword,
        DoubleQuote,
        ToKeyword,
        Arrow,
        WhileKeyword,
        DoKeyword,
        LoopKeyword,
        BreakKeyword,
        ContinueKeyword,
        CaseKeyword,
        SwitchKeyword,
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
        pub const fn row(&self) -> u32 {
            self.position.0
        }
        #[must_use]
        pub const fn col(&self) -> u32 {
            self.position.1
        }

        #[must_use]
        pub const fn position(&self) -> (u32, u32) {
            self.position
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
                Self::Number => "integer",
                Self::P => "p",
                Self::Yarn => "yarn",
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
                Self::Pipe => "\"|\"",
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
            };
            write!(f, "{text_representation}")
        }
    }
}

mod parser {
    use std::fmt;

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
            block: Block<'a>,
            expression: Expression<'a>,
        },
        Loop {
            position: (u32, u32),
            block: Box<Block<'a>>,
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
        position_in_scope: Option<usize>,
        scope_id: Option<usize>,
        identifier: &'a str,
        data_type: DataType<'a>,
        size: usize,
        value: Option<Expression<'a>>,
        is_parameter: bool,
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
        Number(Number),
        // char
        P,
        // string
        Yarn,
        // bool
        Booba,
        // void
        Nopp,
        Struct { name: &'a str },
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Number {
        Pp,
        Spp,
        Xspp,
    }

    #[derive(Clone, Debug)]
    pub struct Struct {}

    #[derive(Clone, Debug, Pos)]
    pub enum Expression<'a> {
        // TODO: Use LiteralExpression instead.
        Number {
            position: (u32, u32),
            number_type: Number,
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

    #[derive(Clone, Debug)]
    pub enum BinaryOperator {
        Add,
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

    #[derive(Clone, Debug)]
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

        /// The size of parameters in instructions.
        pub fn parameters_size(&self) -> usize {
            self.parameters().iter().fold(0, |acc, parameter| {
                acc + parameter.data_type().size_in_instructions()
            })
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
            is_parameter: bool,
        ) -> Self {
            Variable {
                position,
                position_in_scope: None,
                scope_id: None,
                identifier,
                size: data_type.size(),
                data_type,
                value,
                is_parameter,
            }
        }

        pub fn is_initialized(&self) -> bool {
            self.is_parameter || self.value.is_some()
        }

        pub fn position(&self) -> (u32, u32) {
            self.position
        }
        pub fn position_in_scope(&self) -> Option<usize> {
            self.position_in_scope
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

        pub fn set_scope_id(&mut self, scope_id: usize) {
            self.scope_id = Some(scope_id);
        }

        pub fn set_position_in_scope(&mut self, position_in_scope: usize) {
            self.position_in_scope = Some(position_in_scope);
        }

        pub fn size_in_instructions(&self) -> usize {
            ((self.size() - 1) / 4) + 1
        }
        pub fn scope_id(&self) -> Option<usize> {
            self.scope_id
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
                    Number::Pp => std::mem::size_of::<i32>(),
                    Number::Spp => std::mem::size_of::<i16>(),
                    Number::Xspp => std::mem::size_of::<i8>(),
                },
                DataType::P => std::mem::size_of::<char>(),
                DataType::Booba => std::mem::size_of::<bool>(),
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
    use std::cell;
    use std::collections;
    use std::rc;

    use crate::parse::parser::{Block, DataType, Expression, Function, Variable};

    #[derive(Debug)]
    pub struct SymbolTable<'a> {
        /// The global scope holding global variables and function identifiers.
        global_scope: GlobalScope<'a>,
        /// Current stack of function scopes.
        function_scopes: Vec<FunctionScope<'a>>,
    }

    #[derive(Clone, Debug)]
    pub struct Scope<'a> {
        /// Variable symbol table.
        variables: collections::HashMap<&'a str, rc::Rc<Variable<'a>>>,
        /// Function symbol table.
        functions: collections::HashMap<&'a str, rc::Rc<Function<'a>>>,
        id: usize,
    }

    #[derive(Clone, Debug)]
    pub struct GlobalScope<'a> {
        scope: Scope<'a>,
        current_position: usize,
    }

    #[derive(Clone, Debug)]
    pub struct FunctionScope<'a> {
        generated_scopes: Vec<rc::Rc<cell::RefCell<Scope<'a>>>>,
        scope_stack: Vec<rc::Rc<cell::RefCell<Scope<'a>>>>,
        function_identifier: &'a str,
        scope_counter: usize,
        current_position: usize,
    }

    #[derive(Clone, Debug)]
    pub struct VariableDescriptor<'a> {
        position: (u32, u32),
        position_in_scope: usize,
        scope_id: usize,
        data_type: DataType<'a>,
        size: usize,
        value: Option<Expression<'a>>,
        is_parameter: bool,
    }

    #[derive(Clone, Debug)]
    pub struct FunctionDescriptor<'a> {
        position: (u32, u32),
        identifier: &'a str,
        return_type: DataType<'a>,
        parameters: Vec<Variable<'a>>,
        block: Block<'a>,
    }

    impl<'a> SymbolTable<'a> {
        pub fn new() -> Self {
            SymbolTable {
                global_scope: GlobalScope::new(),
                function_scopes: Vec::new(),
            }
        }

        /// Gets the variable from the generated scopes.
        pub fn get_variable_level_and_offset(
            &self,
            identifier: &str,
            function_ident: Option<&'a str>,
        ) -> (u32, usize) {
            if let Some(function_ident) = function_ident {
                if let Some(function_scope) = self.function_scope(function_ident) {
                    if let Some(variable) =
                        function_scope.find_variable_in_generated_scopes(identifier)
                    {
                        return (
                            0,
                            variable
                                .position_in_scope()
                                .expect("Initialized variable position"),
                        );
                    }
                }
            } else {
                return (
                    0,
                    self.global_scope
                        .borrow()
                        .get_variable(identifier)
                        .unwrap_or_else(|| panic!("Unknown variable {identifier}"))
                        .position_in_scope()
                        .expect("Initialized variable position"),
                );
            }

            use std::borrow::Borrow;
            // If not found, try to find it in the global scope.
            (
                1,
                self.global_scope
                    .borrow()
                    .get_variable(identifier)
                    .unwrap_or_else(|| panic!("Unknown variable {identifier}"))
                    .position_in_scope()
                    .expect("Initialized variable position"),
            )
        }

        pub fn push_global_variable(&mut self, variable: Variable<'a>) {
            self.global_scope.push_variable(variable);
        }

        pub fn push_local_variable(&mut self, variable: Variable<'a>) {
            self.current_function_scope_mut().push_variable(variable);
        }

        pub fn has_global_function(&self, identifier: &str) -> bool {
            self.global_scope.has_function(identifier)
        }

        pub fn push_global_function(&mut self, function: Function<'a>) {
            self.global_scope.push_function(function);
        }

        fn push_function_scope(&mut self, function_identifier: &'a str) {
            self.function_scopes
                .push(FunctionScope::new(function_identifier))
        }

        pub fn find_function(&self, identifier: &str) -> Option<&rc::Rc<Function<'a>>> {
            self.global_scope.get_function(identifier)
        }

        pub fn push_scope(&mut self) {
            self.current_function_scope_mut().push_scope();
        }

        pub fn pop_scope(&mut self) {
            self.current_function_scope_mut().pop_scope();
        }

        pub fn find_variable_in_scope_stack(
            &self,
            identifier: &str,
            function_ident: Option<&'a str>,
        ) -> Option<rc::Rc<Variable<'a>>> {
            self.find_local_variable_in_scope_stack(identifier, function_ident)
                .or_else(|| self.find_global_variable(identifier))
        }

        pub fn push_function(&mut self, function: Function<'a>) {
            self.push_function_scope(function.identifier());
        }

        pub fn find_global_variable(&self, identifier: &str) -> Option<rc::Rc<Variable<'a>>> {
            self.global_scope.get_variable(identifier)
        }

        pub fn find_local_variable_in_scope_stack(
            &self,
            identifier: &str,
            function_ident: Option<&'a str>,
        ) -> Option<rc::Rc<Variable<'a>>> {
            self.function_scope(function_ident?)?
                .find_variable_in_scope_stack(identifier)
        }

        // TODO: This could be done in O(1) but w/e.
        pub fn function_scope(&self, function_identifier: &str) -> Option<&FunctionScope<'a>> {
            self.function_scopes
                .iter()
                .find(move |func| func.function_identifier == function_identifier)
        }

        fn current_function_scope_mut(&mut self) -> &mut FunctionScope<'a> {
            self.function_scopes
                .last_mut()
                .expect("Inside function scope")
        }
    }

    impl<'a> Scope<'a> {
        pub fn new(id: usize) -> Self {
            Scope {
                variables: collections::HashMap::new(),
                functions: collections::HashMap::new(),
                id,
            }
        }
        fn push_variable(&mut self, mut variable: Variable<'a>) {
            variable.set_scope_id(self.id);
            self.variables
                .insert(variable.identifier(), rc::Rc::new(variable));
        }

        pub fn get_variable(&self, identifier: &str) -> Option<rc::Rc<Variable<'a>>> {
            if let Some(variable) = self.variables.get(identifier) {
                return Some(variable.clone());
            }
            None
        }

        fn push_function(&mut self, function: Function<'a>) {
            self.functions
                .insert(function.identifier(), rc::Rc::new(function));
        }

        pub fn get_function(&self, identifier: &str) -> Option<&rc::Rc<Function<'a>>> {
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
                scope: Scope::new(0),
                current_position: 1,
            }
        }
        pub fn push_variable(&mut self, mut variable: Variable<'a>) {
            variable.set_position_in_scope(self.current_position);
            self.current_position += variable.size_in_instructions();
            self.scope.push_variable(variable);
        }

        pub fn get_variable(&self, identifier: &str) -> Option<rc::Rc<Variable<'a>>> {
            self.scope.get_variable(identifier)
        }

        pub fn push_function(&mut self, function: Function<'a>) {
            self.scope.push_function(function);
        }

        pub fn get_function(&self, identifier: &str) -> Option<&rc::Rc<Function<'a>>> {
            self.scope.get_function(identifier)
        }

        pub fn has_function(&self, identifier: &str) -> bool {
            self.scope.has_function(identifier)
        }
    }

    impl<'a> FunctionScope<'a> {
        pub const ACTIVATION_RECORD_SIZE: usize = 3;

        pub fn new(function_identifier: &'a str) -> Self {
            FunctionScope {
                generated_scopes: Vec::new(),
                scope_stack: Vec::new(),
                function_identifier,
                scope_counter: 1,
                current_position: Self::ACTIVATION_RECORD_SIZE,
            }
        }

        pub fn find_variable_in_generated_scopes(
            &self,
            identifier: &str,
        ) -> Option<rc::Rc<Variable<'a>>> {
            self.find_variable(identifier, &self.generated_scopes)
        }

        pub fn find_variable_in_scope_stack(
            &self,
            identifier: &str,
        ) -> Option<rc::Rc<Variable<'a>>> {
            self.find_variable(identifier, &self.scope_stack)
        }

        fn find_variable(
            &self,
            identifier: &str,
            scopes: &Vec<rc::Rc<cell::RefCell<Scope<'a>>>>,
        ) -> Option<rc::Rc<Variable<'a>>> {
            // Loop through all scopes to find the variable. If we find a variable
            // with the right identifier make sure it's in the right scope.
            for scope_rc in scopes.iter().rev() {
                let scope = scope_rc.borrow();
                if let Some(variable) = scope.get_variable(identifier) {
                    if variable.scope_id().unwrap() == 0 {}
                    return Some(variable.clone());
                }
            }

            None
        }

        pub fn variable_count(&self) -> usize {
            self.generated_scopes
                .iter()
                .fold(0, |accum, scope| accum + scope.borrow().variables.len())
        }

        pub fn function_identifier(&self) -> &'a str {
            self.function_identifier
        }

        pub fn push_variable(&mut self, mut variable: Variable<'a>) {
            variable.set_position_in_scope(self.current_position);
            self.current_position += variable.size_in_instructions();
            self.current_scope_mut()
                .expect("A scope")
                .borrow_mut()
                .push_variable(variable);
        }

        pub fn push_scope(&mut self) {
            let new_scope = Scope::new(self.scope_counter);
            self.scope_counter += 1;
            let scope = rc::Rc::new(cell::RefCell::new(new_scope));
            self.scope_stack.push(scope.clone());
            self.generated_scopes.push(scope);
        }
        pub fn current_scope_mut(&mut self) -> Option<&mut rc::Rc<cell::RefCell<Scope<'a>>>> {
            self.scope_stack.last_mut()
        }

        pub fn pop_scope(&mut self) {
            self.scope_stack.pop();
        }
    }
}

mod emitter {
    #[derive(Clone, Debug)]
    pub enum Instruction {
        /// Push the literal value arg onto the stack.
        Literal {
            value: i32,
        },
        /// Return from a subroutine. This instruction uses the stack frame (or block mark) from the current invocation of the subroutine to clear the stack of all data local to the current subroutine, restore the base register, and restore the program counter. Like all operations which require no arguments, it uses the op code OPR, with a second argument (here zero) indicating which of the zero-argument operations to perform.
        Operation {
            operation: Operation,
        },
        /// Load (i.e. push onto the stack) the value of the cell identified by level and offset. A level value of 0 means the variable is in the currently executing procedure; 1 means it's in the immediately enclosing region of the program. 2 means it's the region outside that (in PL/0 as in Pascal procedures can nest indefinitely). The offset distinguishes among the variables declared at that level.
        Load {
            level: u32,
            offset: i32,
        },
        /// Store the value currently at the top of the stack to the memory cell identified by level and offset, popping the value off the stack in the process.
        Store {
            level: u32,
            offset: i32,
        },
        /// Call the subroutine at location address, which is level nesting levels different from the nesting level of the currently executing code. This instruction pushes a stack frame (or block mark) onto the stack, storing
        ///
        ///     the base address for variables, level blocks down on the stack (so that variables in outer blocks can be referred to and modified)
        ///     the current base address (so that it can be restored when the subroutine returns)
        ///     the current program counter (so that it can be restored when the subroutine returns)
        Call {
            level: u32,
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
        Label(String),
    }

    #[derive(Clone, Copy, Debug)]
    pub enum Operation {
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
        Absolute(u32),
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

    impl std::fmt::Display for Instruction {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{self:?}")
            // or, alternatively:
            // fmt::Debug::fmt(self, f)
        }
    }

    impl std::fmt::Display for Address {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Absolute(absolute_address) => write!(f, "{absolute_address}")?,
                Self::Label(label) => write!(f, "@{label}")?,
            };

            Ok(())
        }
    }
}

pub mod compiler {
    use std::{cell, error, fs, io, process, rc, time};

    use crate::parse::analysis::SymbolTable;
    use crate::parse::error_diagnosis::SyntaxError;
    use crate::parse::lexer::Token;
    use crate::parse::parser::TranslationUnit;
    use crate::parse::{Emitter, ErrorDiagnosis, Lexer, Parser, SemanticAnalyzer};

    pub struct DppCompiler;

    pub const DEBUG: bool = true;

    impl DppCompiler {
        pub fn compile_translation_unit(
            file_path: &str,
            output_file: &str,
            pl0_interpret_path: &str,
        ) -> Result<(), Box<dyn error::Error>> {
            let file_contents = fs::read_to_string(file_path)?;
            let error_diag = rc::Rc::new(cell::RefCell::new(ErrorDiagnosis::new(
                file_path,
                &file_contents,
            )));

            // Pass error diag to each step.
            println!("Parsing program...");
            let start = time::Instant::now();
            {
                // Lex -> parse -> analyze -> emit.
                let tokens = Self::lex(&file_contents, &error_diag)?;
                let translation_unit = Self::parse(tokens, &error_diag)?;
                dbg!(&translation_unit);
                let symbol_table = Self::analyze(&translation_unit, &error_diag)?;
                Self::emit(output_file, &translation_unit, symbol_table, &error_diag)?;
                error_diag.borrow_mut().check_errors()?;
            }
            let duration = start.elapsed();
            println!("Program parsed in {:?}", duration);

            println!("Running program...");
            let start = time::Instant::now();
            {
                let child = process::Command::new(pl0_interpret_path)
                    .args(["-a", "+d", "+l", "+i", "+t", "+s", output_file])
                    .stdout(process::Stdio::piped())
                    .stderr(process::Stdio::piped())
                    .spawn()?;

                let out = child.wait_with_output()?;
                let stdout = String::from_utf8(out.stdout)?;
                let stderr = String::from_utf8(out.stderr)?;

                if DEBUG {
                    println!("{stdout}");
                }

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
        ) -> Result<SymbolTable<'a>, SyntaxError> {
            SemanticAnalyzer::new(rc::Rc::clone(&error_diag)).analyze(&translation_unit)
        }

        fn emit<'a>(
            output_file: &str,
            translation_unit: &TranslationUnit<'a>,
            symbol_table: SymbolTable<'a>,
            error_diag: &rc::Rc<cell::RefCell<ErrorDiagnosis<'a, '_>>>,
        ) -> io::Result<()> {
            Emitter::new(rc::Rc::new(symbol_table), rc::Rc::clone(&error_diag)).emit_all(
                &mut io::BufWriter::new(fs::File::create(output_file)?),
                &translation_unit,
            )
        }
    }

    #[cfg(test)]
    mod tests {
        #[test]
        fn test() {
            assert_eq!(1, 1);
        }
    }
}
