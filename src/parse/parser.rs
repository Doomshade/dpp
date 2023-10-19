//! For each declaration in grammar we declare an enum and a function that parses that declaration.
//!
//! Each enum always consists of a default variant, usually prefixed by "Invalid" that allows us to
//! continue parsing even though an error occurred. That way we are able to insert a placeholder
//! in the AST and continue parsing. This is useful for error recovery.
//!
//! Each enum also contains a variant for each possible production in the grammar,
//! usually defaulting to one variant with the same name (e.g. `Function::Function`). This adds a
//! little bit of boilerplate, but it allows us to easily add new productions to the grammar.
//!
//! Each enum also derives Debug that lets us print the tree structure of the AST.

use std::cell::RefCell;
use std::fmt::{Debug, Display, Formatter};
use std::rc::Rc;
use dpp_macros::PosMacro;
use dpp_macros_derive::PosMacro;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::lexer::{Token, TokenKind};

pub trait Pos {
    fn row(&self) -> u32;
    fn col(&self) -> u32;
}

#[derive(Clone, Debug)]
pub struct Parser<'a, 'b> {
    tokens: Rc<Vec<Token<'a>>>,
    error_diag: Rc<RefCell<ErrorDiagnosis<'a, 'b>>>,
    curr_token_index: usize,
    position: (u32, u32),
    error: bool,
    // TODO: rename this
    fixing_parsing: bool,
}

#[derive(Clone, Debug, PosMacro)]
pub struct TranslationUnit<'a> {
    position: (u32, u32),
    functions: Vec<Function<'a>>,
    global_statements: Vec<Statement<'a>>,
}

impl<'a> TranslationUnit<'a> {
    pub fn new(functions: Vec<Function<'a>>,
               global_statements: Vec<Statement<'a>>) -> Self {
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

#[derive(Clone, Debug, PosMacro)]
pub struct Function<'a> {
    position: (u32, u32),
    identifier: &'a str,
    return_type: DataType<'a>,
    parameters: Vec<Variable<'a>>,
    block: Block<'a>,
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

#[derive(Clone, Debug)]
pub struct Block<'a> {
    position: (u32, u32),
    statements: Vec<Statement<'a>>,
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

#[derive(Clone, Debug)]
pub struct Variable<'a> {
    position: (u32, u32),
    position_in_scope: Option<u32>,
    identifier: &'a str,
    data_type: DataType<'a>,
    size: usize,
    value: Option<Expression<'a>>,
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
            position_in_scope: None,
            identifier,
            size: data_type.size(),
            data_type,
            value,
        }
    }

    pub fn position(&self) -> (u32, u32) {
        self.position
    }
    pub fn position_in_scope(&self) -> Option<u32> {
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

    pub fn set_position_in_scope(&mut self, position_in_scope: u32) {
        self.position_in_scope = Some(position_in_scope);
    }

    pub fn size_in_instructions(&self) -> usize {
        ((self.size() - 1) / 4) + 1
    }
}

#[derive(Clone, Debug)]
pub enum Statement<'a> {
    VariableDeclaration {
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
}

#[derive(Clone, Debug)]
pub struct Case<'a> {
    expression: Expression<'a>,
    block: Box<Block<'a>>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Number {
    Pp,
    Spp,
    Xspp,
}

#[derive(Clone, Debug)]
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
    Assignment {
        position: (u32, u32),
        identifier: &'a str,
        expression: Box<Expression<'a>>,
    },
    Invalid,
}

impl Display for Expression<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let formatted = match self {
            Expression::Number { value, .. } => value.to_string(),
            Expression::P { value, .. } => value.to_string(),
            Expression::Booba { value, .. } => value.to_string(),
            Expression::Yarn { value, .. } => value.to_string(),
            Expression::Unary { operand, .. } => "Unary expression".to_string(),
            Expression::Binary { .. } => "Binary expression".to_string(),
            Expression::Identifier { identifier, .. } => identifier.to_string(),
            Expression::FunctionCall { identifier, .. } => {
                format!("Function {}", identifier)
            }
            Expression::Assignment { identifier, .. } => identifier.to_string(),
            Expression::Invalid => "Invalid expression".to_string(),
        };
        write!(f, "{}", formatted)?;
        Ok(())
    }
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

impl Display for DataType<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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
            _ => panic!("Invalid data type"),
        }
    }

    pub fn size_in_instructions(&self) -> usize {
        ((self.size() - 1) / 4) + 1
    }
}

#[derive(Clone, Debug)]
pub struct Struct {}

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

impl<'a, 'b> Parser<'a, 'b> {
    pub fn new(
        tokens: Rc<Vec<Token<'a>>>,
        error_diag: Rc<RefCell<ErrorDiagnosis<'a, 'b>>>,
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

    pub fn parse(&mut self) -> TranslationUnit<'a> {
        self.translation_unit()
    }

    fn translation_unit(&mut self) -> TranslationUnit<'a> {
        let mut functions = Vec::<Function<'a>>::new();
        let mut variable_declarations = Vec::<Statement<'a>>::new();
        loop {
            if self.matches_token_kind(TokenKind::FUNcKeyword) {
                if let Some(function) = self.function() {
                    functions.push(function);
                }
            } else if self.matches_data_type() {
                if let Some(var_decl) = self.var_decl() {
                    variable_declarations.push(var_decl);
                }
            } else if self.curr_token_index == self.tokens.len() {
                // We reached the end!
                break;
            } else if let Some(token) = self.token() {
                // We reached the end.. as well!
                if token.kind() == TokenKind::Eof {
                    break;
                }
                // No rewrite function accepted this token in ANY state. Just
                // throw an error, consume the token, and continue parsing.
                self.error_diag.borrow_mut().unexpected_token_error(token);
                self.consume_token();
                self.error = true;
                self.go_into_panic_mode();
            } else {
                panic!("Something unexpected happened :( (compiler error)")
            }
        }
        TranslationUnit::new(functions, variable_declarations)
    }

    fn function(&mut self) -> Option<Function<'a>> {
        let position = self.position;
        self.expect(TokenKind::FUNcKeyword)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let parameters = self.params()?;
        self.expect(TokenKind::Arrow)?;
        let return_type = self.data_type()?;
        let block = self.block()?;

        Some(Function::new(position, identifier, return_type, parameters, block))
    }

    fn params(&mut self) -> Option<Vec<Variable<'a>>> {
        // TODO: Create a params variant.
        self.expect(TokenKind::OpenParen)?;
        let mut parameters = Vec::<Variable<'a>>::new();

        // Check if the close parenthesis is present first,
        // then try to parse a parameter. If a parameter is present,
        // check if "," or the close parenthesis is there.
        // If neither is there, we say we expected
        if self.matches_token_kind(TokenKind::CloseParen) {
            self.expect(TokenKind::CloseParen)?;
            return Some(parameters);
        }

        let parameter = self.parameter()?;
        parameters.push(parameter);

        let mut invalid_params = false;
        while !self.matches_token_kind(TokenKind::CloseParen) {
            if invalid_params {
                self.add_error("parameter");
                self.consume_token();
            } else {
                invalid_params = invalid_params || self.expect(TokenKind::Comma).is_none();
                if !invalid_params {
                    let parameter = self.parameter();
                    invalid_params = invalid_params || parameter.is_none();
                    parameters.push(parameter?);
                }
            }
        }
        self.expect(TokenKind::CloseParen)?;

        Some(parameters)
    }

    fn parameter(&mut self) -> Option<Variable<'a>> {
        let position = self.position;
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Colon)?;
        let data_type = self.data_type()?;
        Some(Variable::new(position, identifier, data_type, None))
    }

    fn block(&mut self) -> Option<Block<'a>> {
        let position = self.position;
        self.expect(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement<'a>>::new();

        while !self.matches_token_kind(TokenKind::CloseBrace) {
            if let Some(statement) = self.statement() {
                statements.push(statement);
            }
        }
        self.expect(TokenKind::CloseBrace)?;

        Some(Block::new(position, statements))
    }

    // Wrappers for print! and println! macros to use
    // inside the Statement::PrintStatement.
    fn print(str: &str) {
        print!("{str}");
    }
    fn println(str: &str) {
        println!("{str}");
    }

    fn statement(&mut self) -> Option<Statement<'a>> {
        let token_kind = self.token()?.kind();

        return match token_kind {
            TokenKind::IfKeyword => {
                self.expect(TokenKind::IfKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;

                let statement = self.statement()?;
                if self.matches_token_kind(TokenKind::ElseKeyword) {
                    self.expect(TokenKind::ElseKeyword)?;
                    let else_statement = self.statement()?;
                    Some(Statement::IfElse {
                        position: self.position,
                        expression,
                        statement: Box::new(statement),
                        else_statement: Box::new(else_statement),
                    })
                } else {
                    Some(Statement::If {
                        position: self.position,
                        expression,
                        statement: Box::new(statement),
                    })
                }
            }
            TokenKind::ForKeyword => {
                self.expect(TokenKind::ForKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let index_ident = self.expect(TokenKind::Identifier)?;
                let ident_expression = if self.matches_token_kind(TokenKind::Equal) {
                    self.expect(TokenKind::Equal)?;
                    Some(self.expr()?)
                } else {
                    None
                };
                self.expect(TokenKind::ToKeyword)?;
                let length_expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                let statement = self.statement()?;

                return Some(Statement::For {
                    position: self.position,
                    index_ident,
                    ident_expression,
                    length_expression,
                    statement: Box::new(statement),
                });
            }
            TokenKind::WhileKeyword => {
                self.expect(TokenKind::WhileKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                let statement = self.statement()?;

                return Some(Statement::While {
                    position: self.position,
                    expression,
                    statement: Box::new(statement),
                });
            }
            TokenKind::DoKeyword => {
                self.expect(TokenKind::DoKeyword)?;
                let block = self.block()?;
                self.expect(TokenKind::WhileKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::DoWhile {
                    position: self.position,
                    block,
                    expression,
                });
            }
            TokenKind::LoopKeyword => {
                self.expect(TokenKind::LoopKeyword)?;
                let block = self.block()?;
                return Some(Statement::Loop {
                    position: self.position,
                    block: Box::new(block),
                });
            }
            TokenKind::BreakKeyword => {
                self.expect(TokenKind::BreakKeyword)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Break {
                    position: self.position,
                });
            }
            TokenKind::ContinueKeyword => {
                self.expect(TokenKind::ContinueKeyword)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Continue {
                    position: self.position,
                });
            }
            TokenKind::SwitchKeyword => {
                self.expect(TokenKind::SwitchKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                self.expect(TokenKind::OpenBrace)?;
                let mut cases = Vec::<Case<'a>>::new();
                if self.matches_token_kind(TokenKind::CloseBrace) {
                    self.expect(TokenKind::CloseBrace)?;
                    return Some(Statement::Switch {
                        position: self.position,
                        expression,
                        cases,
                    });
                }

                cases.push(self.case()?);
                while !self.matches_token_kind(TokenKind::CloseBrace) {
                    self.expect(TokenKind::Comma);
                    cases.push(self.case()?);
                }

                self.expect(TokenKind::CloseBrace)?;
                return Some(Statement::Switch {
                    position: self.position,
                    expression,
                    cases,
                });
            }
            TokenKind::ByeKeyword => {
                self.expect(TokenKind::ByeKeyword)?;
                if let Some(expression) = self.expr() {
                    let ret = Statement::Bye {
                        position: self.position,
                        expression: Some(expression),
                    };
                    self.expect(TokenKind::Semicolon)?;
                    return Some(ret);
                }

                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Bye {
                    position: self.position,
                    expression: None,
                });
            }
            TokenKind::PprintlnKeyword | TokenKind::PprintKeyword => {
                self.expect_one_from(&[TokenKind::PprintKeyword, TokenKind::PprintlnKeyword])?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                self.expect(TokenKind::Semicolon)?;

                return Some(Statement::Print {
                    position: self.position,
                    print_function: match token_kind {
                        TokenKind::PprintKeyword => Self::print,
                        TokenKind::PprintlnKeyword => Self::println,
                        _ => unreachable!(),
                    },
                    expression,
                });
            }
            TokenKind::Semicolon => {
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Empty {
                    position: self.position,
                });
            }
            TokenKind::YemKeyword
            | TokenKind::NomKeyword
            | TokenKind::Number
            | TokenKind::Yarn
            | TokenKind::OpenParen
            | TokenKind::Identifier => {
                let expression = self.expr()?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Expression {
                    position: self.position,
                    expression,
                });
            }
            TokenKind::OpenBrace => {
                let block = self.block()?;
                return Some(Statement::Block {
                    position: self.position,
                    block: Box::new(block),
                });
            }
            TokenKind::XxlppKeyword
            | TokenKind::PpKeyword
            | TokenKind::SppKeyword
            | TokenKind::XsppKeyword
            | TokenKind::PKeyword
            | TokenKind::NoppKeyword
            | TokenKind::BoobaKeyword
            | TokenKind::YarnKeyword => {
                let variable_declaration = self.var_decl()?;
                return Some(variable_declaration);
            }
            _ => {
                self.error = true;
                self.go_into_panic_mode();
                return self.statement();
            }
        };
    }

    fn case(&mut self) -> Option<Case<'a>> {
        self.expect(TokenKind::CaseKeyword)?;
        let expression = self.expr()?;
        let block = self.block()?;
        Some(Case {
            expression,
            block: Box::new(block),
        })
    }

    fn var_decl(&mut self) -> Option<Statement<'a>> {
        let data_type = self.data_type()?;
        self.expect(TokenKind::Arrow)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let statement = if self.matches_token_kind(TokenKind::Equal) {
            self.expect(TokenKind::Equal);
            let expression = self.expr()?;
            Statement::VariableDeclaration {
                variable: Variable::new(self.position, identifier, data_type, Some(expression)),
            }
        } else {
            Statement::VariableDeclaration {
                variable: Variable::new(self.position, identifier, data_type, None),
            }
        };

        self.expect(TokenKind::Semicolon)?;
        Some(statement)
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

    fn data_type(&mut self) -> Option<DataType<'a>> {
        let token = self.expect_one_from(&[
            TokenKind::XxlppKeyword,
            TokenKind::PpKeyword,
            TokenKind::SppKeyword,
            TokenKind::XsppKeyword,
            TokenKind::PKeyword,
            TokenKind::NoppKeyword,
            TokenKind::BoobaKeyword,
            TokenKind::YarnKeyword,
        ])?;

        match token.1 {
            TokenKind::PpKeyword => Some(DataType::Number(Number::Pp)),
            TokenKind::SppKeyword => Some(DataType::Number(Number::Spp)),
            TokenKind::XsppKeyword => Some(DataType::Number(Number::Xspp)),
            TokenKind::PKeyword => Some(DataType::P),
            TokenKind::NoppKeyword => Some(DataType::Nopp),
            TokenKind::BoobaKeyword => Some(DataType::Booba),
            TokenKind::YarnKeyword => Some(DataType::Yarn),
            _ => None,
        }
    }

    fn _struct_(&mut self) -> DataType<'a> {
        todo!()
    }

    fn expr(&mut self) -> Option<Expression<'a>> {
        self.equ()
    }

    fn equ(&mut self) -> Option<Expression<'a>> {
        let mut expr = self.comp()?;

        while self.matches_token_kind(TokenKind::BangEqual)
            || self.matches_token_kind(TokenKind::EqualEqual)
        {
            let op = match self.token()?.kind() {
                TokenKind::BangEqual => BinaryOperator::NotEqual,
                TokenKind::EqualEqual => BinaryOperator::Equal,
                _ => unreachable!(),
            };
            self.consume_token();

            let rhs = self.comp()?;
            expr = Expression::Binary {
                position: self.position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn comp(&mut self) -> Option<Expression<'a>> {
        let mut expr = self.term()?;

        while self.matches_token_kind(TokenKind::Greater)
            || self.matches_token_kind(TokenKind::GreaterEqual)
            || self.matches_token_kind(TokenKind::Less)
            || self.matches_token_kind(TokenKind::LessEqual)
        {
            let op = match self.token()?.kind() {
                TokenKind::Greater => BinaryOperator::GreaterThan,
                TokenKind::GreaterEqual => BinaryOperator::GreaterThanOrEqual,
                TokenKind::Less => BinaryOperator::LessThan,
                TokenKind::LessEqual => BinaryOperator::LessThanOrEqual,
                _ => unreachable!(),
            };
            self.consume_token();
            let rhs = self.term()?;

            expr = Expression::Binary {
                position: self.position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn term(&mut self) -> Option<Expression<'a>> {
        let mut expr = self.factor()?;

        while self.matches_token_kind(TokenKind::Dash) || self.matches_token_kind(TokenKind::Plus) {
            let op = match self.token()?.kind() {
                TokenKind::Dash => BinaryOperator::Subtract,
                TokenKind::Plus => BinaryOperator::Add,
                _ => unreachable!(),
            };
            self.consume_token();
            let rhs = self.factor()?;

            expr = Expression::Binary {
                position: self.position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn factor(&mut self) -> Option<Expression<'a>> {
        let mut expr = self.unary()?;

        while self.matches_token_kind(TokenKind::ForwardSlash)
            || self.matches_token_kind(TokenKind::Star)
        {
            let op = match self.token()?.kind() {
                TokenKind::ForwardSlash => BinaryOperator::Divide,
                TokenKind::Star => BinaryOperator::Multiply,
                _ => unreachable!(),
            };
            self.consume_token();
            let rhs = self.unary()?;
            expr = Expression::Binary {
                position: self.position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }
        Some(expr)
    }

    fn unary(&mut self) -> Option<Expression<'a>> {
        if self.matches_token_kind(TokenKind::Bang) || self.matches_token_kind(TokenKind::Dash) {
            let op = match self.token()?.kind() {
                TokenKind::Bang => UnaryOperator::Not,
                TokenKind::Dash => UnaryOperator::Negate,
                _ => unreachable!(),
            };
            self.consume_token();
            let operand = self.unary()?;
            Some(Expression::Unary {
                position: self.position,
                op,
                operand: Box::new(operand),
            })
        } else {
            self.primary()
        }
    }

    fn primary(&mut self) -> Option<Expression<'a>> {
        match self.token()?.kind() {
            TokenKind::Identifier => {
                let identifier = self.expect(TokenKind::Identifier)?;
                match self.token()?.kind() {
                    TokenKind::OpenParen => {
                        let arguments = self.args()?;
                        Some(Expression::FunctionCall {
                            position: self.position,
                            identifier,
                            arguments,
                        })
                    }
                    TokenKind::Equal => {
                        self.expect(TokenKind::Equal)?;
                        let expression = self.expr()?;
                        Some(Expression::Assignment {
                            position: self.position,
                            identifier,
                            expression: Box::new(expression),
                        })
                    }
                    _ => Some(Expression::Identifier {
                        position: self.position,
                        identifier,
                    }),
                }
            }
            TokenKind::YemKeyword => {
                self.expect(TokenKind::YemKeyword)?;
                Some(Expression::Booba {
                    position: self.position,
                    value: true,
                })
            }
            TokenKind::NomKeyword => {
                self.expect(TokenKind::NomKeyword)?;
                Some(Expression::Booba {
                    position: self.position,
                    value: false,
                })
            }
            TokenKind::Number => {
                let number = self.expect(TokenKind::Number)?;
                if let Ok(value) = number.parse::<i32>() {
                    Some(Expression::Number {
                        position: self.position,
                        number_type: Number::Pp,
                        value,
                    })
                } else {
                    panic!("Invalid number")
                }
            }
            TokenKind::P => {
                let char = self.expect(TokenKind::P)?;
                if let Some(value) = char.chars().next() {
                    Some(Expression::P {
                        position: self.position,
                        value,
                    })
                } else {
                    panic!("Invalid character")
                }
            }
            TokenKind::Yarn => {
                let yarn = self.expect(TokenKind::Yarn)?;
                Some(Expression::Yarn {
                    position: self.position,
                    value: yarn,
                })
            }
            TokenKind::OpenParen => {
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                Some(expression)
            }
            _ => {
                self.add_error("expression");
                // Return some here to let the callee handle this.
                Some(Expression::Invalid)
            }
        }
    }

    fn args(&mut self) -> Option<Vec<Expression<'a>>> {
        self.expect(TokenKind::OpenParen)?;
        let mut args = Vec::<Expression<'a>>::new();

        if self.matches_token_kind(TokenKind::CloseParen) {
            self.expect(TokenKind::CloseParen)?;
            return Some(args);
        }

        let arg = self.expr()?;
        args.push(arg);
        while !self.matches_token_kind(TokenKind::CloseParen) {
            self.expect(TokenKind::Comma)?;
            args.push(self.expr()?);
        }
        self.expect(TokenKind::CloseParen)?;
        Some(args)
    }
}
