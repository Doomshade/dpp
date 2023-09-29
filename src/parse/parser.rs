//! For each declaration in grammar we declare an enum and a function that parses that declaration.
//!
//! Each enum always consists of a default variant, usually prefixed by "Invalid" that allows us to
//! continue parsing even though an error occurred. That way we are able to insert a placeholder
//! in the AST and continue parsing. This is useful for error recovery.
//!
//! Each enum also contains a variant for each possible production in the grammar,
//! usually defaulting to one variant with the same name (e.g. Function::Function). This adds a
//! little bit of boilerplate, but it allows us to easily add new productions to the grammar.
//!
//! Each enum also derives Debug that lets us print the tree structure of the AST.

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::lexer::{Token, TokenKind};
use std::cell::RefCell;
use std::sync::Arc;

#[derive(Debug)]
pub struct Parser<'a> {
    tokens: Arc<Vec<Token<'a>>>,
    error_diag: Arc<RefCell<ErrorDiagnosis>>,
    curr_token_index: usize,
    position: (u32, u32),
    error: bool,
}

#[derive(Debug)]
pub struct TranslationUnit {
    pub functions: Vec<Function>,
    pub variables: Vec<Statement>,
}

#[derive(Debug)]
pub struct Function {
    pub position: (u32, u32),
    pub identifier: String,
    pub return_type: DataType,
    pub parameters: Vec<Parameter>,
    pub block: Block,
}

#[derive(Debug)]
pub struct Parameters {
    position: (u32, u32),
    parameters: Vec<Parameter>,
}

#[derive(Debug)]
pub struct Parameter {
    position: (u32, u32),
    pub identifier: String,
    pub data_type: DataType,
}

#[derive(Debug)]
pub struct Block {
    position: (u32, u32),
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Variable {
    pub position: (u32, u32),
    pub identifier: String,
    pub data_type: DataType,
}

#[derive(Debug)]
pub enum Statement {
    VariableDeclaration {
        variable: Variable,
    },
    VariableDeclarationAndAssignment {
        variable: Variable,
        expression: Expression,
    },
    IfStatement {
        position: (u32, u32),
        expression: Expression,
        statement: Box<Statement>,
    },
    IfElseStatement {
        position: (u32, u32),
        expression: Expression,
        statement: Box<Statement>,
        else_statement: Box<Statement>,
    },
    ByeStatement {
        position: (u32, u32),
        expression: Expression,
    },
    PprintStatement {
        position: (u32, u32),
        expression: Expression,
    },
    BlockStatement {
        position: (u32, u32),
        block: Box<Block>,
    },
    ExpressionStatement {
        position: (u32, u32),
        expression: Expression,
    },
    EmptyStatement {
        position: (u32, u32),
    },
    ForStatement {
        position: (u32, u32),
        index_ident: String,
        length_expression: Expression,
        statement: Box<Statement>,
    },
    ForStatementWithIdentExpression {
        position: (u32, u32),
        ident: Expression,
        length_expression: Expression,
        statement: Box<Statement>,
    },
    WhileStatement {
        position: (u32, u32),
        expression: Expression,
        statement: Box<Statement>,
    },
    DoWhileStatement {
        position: (u32, u32),
        block: Block,
        expression: Expression,
    },
    LoopStatement {
        position: (u32, u32),
        block: Box<Block>,
    },
    BreakStatement {
        position: (u32, u32),
    },
    ContinueStatement {
        position: (u32, u32),
    },
    SwitchStatement {
        position: (u32, u32),
        expression: Expression,
        cases: Vec<Case>,
    },
}

#[derive(Debug)]
pub struct Case {
    expression: Expression,
    block: Box<Block>,
}

#[derive(Debug)]
pub enum Expression {
    PpExpression {
        position: (u32, u32),
        pp: i32,
    },
    BoobaExpression {
        position: (u32, u32),
        booba: bool,
    },
    YarnExpression {
        position: (u32, u32),
        yarn: String,
    },
    UnaryExpression {
        position: (u32, u32),
        op: UnaryOperator,
        operand: Box<Expression>,
    },
    BinaryExpression {
        position: (u32, u32),
        lhs: Box<Expression>,
        op: BinaryOperator,
        rhs: Box<Expression>,
    },
    IdentifierExpression {
        position: (u32, u32),
        identifier: String,
    },
    FunctionCall {
        position: (u32, u32),
        identifier: String,
        arguments: Vec<Expression>,
    },
    AssignmentExpression {
        position: (u32, u32),
        identifier: String,
        expression: Box<Expression>,
    },
    InvalidExpression,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum DataType {
    // u64
    Xxlpp,
    // u32
    Pp,
    // u16
    Spp,
    // u8
    Xspp,
    // char
    P,
    // string
    Yarn,
    // bool
    Booba,
    // void
    Nopp,
    Struct { name: String },
}

#[derive(Debug)]
pub struct Struct {}

#[derive(Debug)]
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

#[derive(Debug)]
pub enum UnaryOperator {
    Not,
    Negate,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: Arc<Vec<Token<'a>>>, error_diag: Arc<RefCell<ErrorDiagnosis>>) -> Self {
        Self {
            position: (1, 1),
            tokens,
            curr_token_index: 0,
            error_diag,
            error: false,
        }
    }

    fn consume_token(&mut self) {
        self.curr_token_index += 1;
        if let Some(token) = self.token() {
            self.position = token.position();
        }
    }

    #[must_use]
    fn token(&self) -> Option<&Token> {
        return self.token_offset(0);
    }

    #[must_use]
    fn token_offset(&self, offset: i32) -> Option<&Token> {
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
    fn expect(&mut self, token_kind: TokenKind) -> Option<String> {
        if let Some(token) = self.token() {
            if token.kind() == token_kind {
                let token_value = token.value();
                self.error = false;
                self.consume_token();
                if let Some(token_value) = token_value {
                    return Some(token_value);
                }
                return Some(String::new());
            }

            // Check if this is the second error in a row.
            // If it is, return None. This will signal that we should go into panic mode.
            // We let the callee handle this.
            if self.error {
                return None;
            }

            // Log the error at the previous token as we expected something else there.
            if let Some(prev_token) = self.token_offset(-1) {
                self.error_diag
                    .borrow_mut()
                    .expected_different_token_error(prev_token, token_kind);
                self.error = true;
            } else {
                self.error_diag.borrow_mut().handle("No token found");
                self.error = true;
            }
            return Some(String::new());
        }

        self.error_diag.borrow_mut().handle("No token found");
        self.error = true;
        Some(String::new())
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

    pub fn parse(&mut self) -> TranslationUnit {
        self.translation_unit()
    }

    fn translation_unit(&mut self) -> TranslationUnit {
        let mut functions = Vec::<Function>::new();
        let mut variable_declarations = Vec::<Statement>::new();
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
                self.error_diag.borrow_mut().invalid_token_error(token);
                self.consume_token();
                self.error = true;
                self.go_into_panic_mode();
            } else {
                panic!("Something unexpected happened :( (compiler error)")
            }
        }
        TranslationUnit {
            functions,
            variables: variable_declarations,
        }
    }

    fn function(&mut self) -> Option<Function> {
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

    fn params(&mut self) -> Option<Vec<Parameter>> {
        self.expect(TokenKind::OpenParen)?;
        let mut parameters = Vec::<Parameter>::new();

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

    fn parameter(&mut self) -> Option<Parameter> {
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Colon)?;
        let data_type = self.data_type()?;
        Some(Parameter {
            position: self.position,
            identifier,
            data_type,
        })
    }

    fn block(&mut self) -> Option<Block> {
        self.expect(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement>::new();

        while !self.matches_token_kind(TokenKind::CloseBrace) {
            if let Some(statement) = self.statement() {
                statements.push(statement);
            }
        }
        self.expect(TokenKind::CloseBrace)?;

        Some(Block {
            position: self.position,
            statements,
        })
    }

    fn statement(&mut self) -> Option<Statement> {
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
                let ident_expression: Option<Expression>;
                if self.matches_token_kind(TokenKind::Equal) {
                    self.expect(TokenKind::Equal)?;
                    ident_expression = Some(self.expr()?);
                } else {
                    ident_expression = None;
                }
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
                let mut cases = Vec::<Case>::new();
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
                let expression = self.expr()?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::ByeStatement {
                    position: self.position,
                    expression,
                });
            }
            TokenKind::PprintKeyword => {
                self.expect(TokenKind::PprintKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::PprintStatement {
                    position: self.position,
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

    fn case(&mut self) -> Option<Case> {
        self.expect(TokenKind::CaseKeyword)?;
        let expression = self.expr()?;
        let block = self.block()?;
        Some(Case {
            expression,
            block: Box::new(block),
        })
    }

    fn var_decl(&mut self) -> Option<Statement> {
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

    fn data_type(&mut self) -> Option<DataType> {
        if let Some(token) = self.token() {
            return match token.kind() {
                TokenKind::XxlppKeyword => {
                    self.consume_token();
                    Some(DataType::Xxlpp)
                }
                TokenKind::PpKeyword => {
                    self.consume_token();
                    Some(DataType::Pp)
                }
                TokenKind::SppKeyword => {
                    self.consume_token();
                    Some(DataType::Spp)
                }
                TokenKind::XsppKeyword => {
                    self.consume_token();
                    Some(DataType::Xspp)
                }
                TokenKind::PKeyword => {
                    self.consume_token();
                    Some(DataType::P)
                }
                TokenKind::NoppKeyword => {
                    self.consume_token();
                    Some(DataType::Nopp)
                }
                TokenKind::BoobaKeyword => {
                    self.consume_token();
                    Some(DataType::Booba)
                }
                TokenKind::YarnKeyword => {
                    self.consume_token();
                    Some(DataType::Yarn)
                }
                _ => None,
            };
        }
        None
    }

    fn _struct_(&mut self) -> DataType {
        todo!()
    }

    fn expr(&mut self) -> Option<Expression> {
        self.equ()
    }

    fn equ(&mut self) -> Option<Expression> {
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

    fn comp(&mut self) -> Option<Expression> {
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

    fn term(&mut self) -> Option<Expression> {
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

    fn factor(&mut self) -> Option<Expression> {
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

    fn unary(&mut self) -> Option<Expression> {
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

    fn primary(&mut self) -> Option<Expression> {
        match self.token()?.kind() {
            TokenKind::Identifier => {
                let identifier = self.expect(TokenKind::Identifier)?;
                return match self.token()?.kind() {
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
                };
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
                Some(Expression::PpExpression {
                    position: self.position,
                    pp: number.parse::<i32>().unwrap(),
                })
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

    fn args(&mut self) -> Option<Vec<Expression>> {
        self.expect(TokenKind::OpenParen)?;
        let mut args = Vec::<Expression>::new();

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
