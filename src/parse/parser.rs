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
use std::fmt::Debug;
use std::rc::Rc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::lexer::{Token, TokenKind};

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

#[derive(Clone, Debug)]
pub struct TranslationUnit<'a> {
    pub functions: Vec<Function<'a>>,
    pub global_statements: Vec<Statement<'a>>,
}

#[derive(Clone, Debug)]
pub struct Function<'a> {
    pub position: (u32, u32),
    pub identifier: &'a str,
    pub return_type: DataType<'a>,
    pub parameters: Vec<Parameter<'a>>,
    pub block: Block<'a>,
}

#[derive(Clone, Debug)]
pub struct Parameters<'a> {
    position: (u32, u32),
    parameters: Vec<Parameter<'a>>,
}

#[derive(Clone, Debug)]
pub struct Parameter<'a> {
    position: (u32, u32),
    pub identifier: &'a str,
    pub data_type: DataType<'a>,
}

#[derive(Clone, Debug)]
pub struct Block<'a> {
    pub position: (u32, u32),
    pub statements: Vec<Statement<'a>>,
}

#[derive(Clone, Debug)]
pub struct Variable<'a> {
    pub position: (u32, u32),
    pub identifier: &'a str,
    pub data_type: DataType<'a>,
}

#[derive(Clone, Debug)]
pub enum Statement<'a> {
    VariableDeclaration {
        variable: Variable<'a>,
    },
    VariableDeclarationAndAssignment {
        variable: Variable<'a>,
        expression: Expression<'a>,
    },
    IfStatement {
        position: (u32, u32),
        expression: Expression<'a>,
        statement: Box<Statement<'a>>,
    },
    IfElseStatement {
        position: (u32, u32),
        expression: Expression<'a>,
        statement: Box<Statement<'a>>,
        else_statement: Box<Statement<'a>>,
    },
    ByeStatement {
        position: (u32, u32),
        expression: Option<Expression<'a>>,
    },
    PrintStatement {
        position: (u32, u32),
        print_function: fn(&str),
        expression: Expression<'a>,
    },
    BlockStatement {
        position: (u32, u32),
        block: Box<Block<'a>>,
    },
    ExpressionStatement {
        position: (u32, u32),
        expression: Expression<'a>,
    },
    EmptyStatement {
        position: (u32, u32),
    },
    ForStatement {
        position: (u32, u32),
        index_ident: &'a str,
        length_expression: Expression<'a>,
        statement: Box<Statement<'a>>,
    },
    ForStatementWithIdentExpression {
        position: (u32, u32),
        ident: Expression<'a>,
        length_expression: Expression<'a>,
        statement: Box<Statement<'a>>,
    },
    WhileStatement {
        position: (u32, u32),
        expression: Expression<'a>,
        statement: Box<Statement<'a>>,
    },
    DoWhileStatement {
        position: (u32, u32),
        block: Block<'a>,
        expression: Expression<'a>,
    },
    LoopStatement {
        position: (u32, u32),
        block: Box<Block<'a>>,
    },
    BreakStatement {
        position: (u32, u32),
    },
    ContinueStatement {
        position: (u32, u32),
    },
    SwitchStatement {
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

#[derive(Debug, PartialEq, Clone)]
pub enum Number {
    Pp,
    Spp,
    Xspp,
}

#[derive(Clone, Debug)]
pub enum Expression<'a> {
    NumberExpression {
        position: (u32, u32),
        number_type: Number,
        value: i32,
    },
    PExpression {
        position: (u32, u32),
        value: char,
    },
    BoobaExpression {
        position: (u32, u32),
        booba: bool,
    },
    YarnExpression {
        position: (u32, u32),
        yarn: &'a str,
    },
    UnaryExpression {
        position: (u32, u32),
        op: UnaryOperator,
        operand: Box<Expression<'a>>,
    },
    BinaryExpression {
        position: (u32, u32),
        lhs: Box<Expression<'a>>,
        op: BinaryOperator,
        rhs: Box<Expression<'a>>,
    },
    IdentifierExpression {
        position: (u32, u32),
        identifier: &'a str,
    },
    FunctionCall {
        position: (u32, u32),
        identifier: &'a str,
        arguments: Vec<Expression<'a>>,
    },
    AssignmentExpression {
        position: (u32, u32),
        identifier: &'a str,
        expression: Box<Expression<'a>>,
    },
    InvalidExpression,
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
        match (self, other) {
            (DataType::Number(..), DataType::Number(..)) => true,
            (DataType::P, DataType::P) => true,
            (DataType::Yarn, DataType::Yarn) => true,
            (DataType::Booba, DataType::Booba) => true,
            (DataType::Nopp, DataType::Nopp) => true,
            _ => false,
        }
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
        TranslationUnit {
            functions,
            global_statements: variable_declarations,
        }
    }

    fn function(&mut self) -> Option<Function<'a>> {
        self.expect(TokenKind::FUNcKeyword)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let parameters = self.params()?;
        self.expect(TokenKind::Arrow)?;
        let return_type = self.data_type()?;
        let block = self.block()?;

        Some(Function {
            position: self.position,
            identifier,
            return_type,
            parameters,
            block,
        })
    }

    fn params(&mut self) -> Option<Vec<Parameter<'a>>> {
        self.expect(TokenKind::OpenParen)?;
        let mut parameters = Vec::<Parameter<'a>>::new();

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

    fn parameter(&mut self) -> Option<Parameter<'a>> {
        let identifier = self.expect(TokenKind::Identifier)?;
        dbg!(self.token());
        self.expect(TokenKind::Colon)?;
        dbg!(self.token());
        let data_type = self.data_type()?;
        Some(Parameter {
            position: self.position,
            identifier,
            data_type,
        })
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

        Some(Block {
            position,
            statements,
        })
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
                    Some(Statement::IfElseStatement {
                        position: self.position,
                        expression,
                        statement: Box::new(statement),
                        else_statement: Box::new(else_statement),
                    })
                } else {
                    Some(Statement::IfStatement {
                        position: self.position,
                        expression,
                        statement: Box::new(statement),
                    })
                }
            }
            TokenKind::ForKeyword => {
                self.expect(TokenKind::ForKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let ident = self.expect(TokenKind::Identifier)?;
                let ident_expression = if self.matches_token_kind(TokenKind::Equal) {
                    self.expect(TokenKind::Equal)?;
                    Some(self.expr()?)
                } else {
                    None
                };
                self.expect(TokenKind::ToKeyword)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                let statement = self.statement()?;

                if let Some(ident_expression) = ident_expression {
                    return Some(Statement::ForStatementWithIdentExpression {
                        position: self.position,
                        ident: ident_expression,
                        length_expression: expression,
                        statement: Box::new(statement),
                    });
                }

                return Some(Statement::ForStatement {
                    position: self.position,
                    index_ident: ident,
                    length_expression: expression,
                    statement: Box::new(statement),
                });
            }
            TokenKind::WhileKeyword => {
                self.expect(TokenKind::WhileKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                let statement = self.statement()?;

                return Some(Statement::WhileStatement {
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
                return Some(Statement::DoWhileStatement {
                    position: self.position,
                    block,
                    expression,
                });
            }
            TokenKind::LoopKeyword => {
                self.expect(TokenKind::LoopKeyword)?;
                let block = self.block()?;
                return Some(Statement::LoopStatement {
                    position: self.position,
                    block: Box::new(block),
                });
            }
            TokenKind::BreakKeyword => {
                self.expect(TokenKind::BreakKeyword)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::BreakStatement {
                    position: self.position,
                });
            }
            TokenKind::ContinueKeyword => {
                self.expect(TokenKind::ContinueKeyword)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::ContinueStatement {
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
                    return Some(Statement::SwitchStatement {
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
                return Some(Statement::SwitchStatement {
                    position: self.position,
                    expression,
                    cases,
                });
            }
            TokenKind::ByeKeyword => {
                self.expect(TokenKind::ByeKeyword)?;
                if let Some(expression) = self.expr() {
                    let ret = Statement::ByeStatement {
                        position: self.position,
                        expression: Some(expression),
                    };
                    self.expect(TokenKind::Semicolon)?;
                    return Some(ret);
                }

                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::ByeStatement {
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

                return Some(Statement::PrintStatement {
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
                return Some(Statement::EmptyStatement {
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
                return Some(Statement::ExpressionStatement {
                    position: self.position,
                    expression,
                });
            }
            TokenKind::OpenBrace => {
                let block = self.block()?;
                return Some(Statement::BlockStatement {
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
            Statement::VariableDeclarationAndAssignment {
                variable: Variable {
                    position: self.position,
                    identifier,
                    data_type,
                },
                expression,
            }
        } else {
            Statement::VariableDeclaration {
                variable: Variable {
                    position: self.position,
                    identifier,
                    data_type,
                },
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
            expr = Expression::BinaryExpression {
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

            expr = Expression::BinaryExpression {
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

            expr = Expression::BinaryExpression {
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
            expr = Expression::BinaryExpression {
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
            Some(Expression::UnaryExpression {
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
                        Some(Expression::AssignmentExpression {
                            position: self.position,
                            identifier,
                            expression: Box::new(expression),
                        })
                    }
                    _ => Some(Expression::IdentifierExpression {
                        position: self.position,
                        identifier,
                    }),
                }
            }
            TokenKind::YemKeyword => {
                self.expect(TokenKind::YemKeyword)?;
                Some(Expression::BoobaExpression {
                    position: self.position,
                    booba: true,
                })
            }
            TokenKind::NomKeyword => {
                self.expect(TokenKind::NomKeyword)?;
                Some(Expression::BoobaExpression {
                    position: self.position,
                    booba: false,
                })
            }
            TokenKind::Number => {
                let number = self.expect(TokenKind::Number)?;
                if let Ok(value) = number.parse::<i32>() {
                    Some(Expression::NumberExpression {
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
                    Some(Expression::PExpression {
                        position: self.position,
                        value,
                    })
                } else {
                    panic!("Invalid character")
                }
            }
            TokenKind::Yarn => {
                let yarn = self.expect(TokenKind::Yarn)?;
                Some(Expression::YarnExpression {
                    position: self.position,
                    yarn,
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
                Some(Expression::InvalidExpression)
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
