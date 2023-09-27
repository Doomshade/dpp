use std::cell::RefCell;
use std::fmt::Debug;
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::{
    BinaryOperator, Block, Case, DataType, Expression, Function, Parameter, Parser, Statement,
    Token, TokenKind, TranslationUnit, UnaryOperator,
};

impl Parser {
    pub fn new(tokens: Arc<Vec<Token>>, error_diag: Arc<RefCell<ErrorDiagnosis>>) -> Self {
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

    fn binop(&mut self, op_matcher: fn(&TokenKind) -> BinaryOperator) -> BinaryOperator {
        let operator = self.token().expect("Failed to get token");
        let kind = &operator.kind();
        let op = op_matcher(kind);
        self.consume_token();
        op
    }

    fn unop(&mut self, op_matcher: fn(&TokenKind) -> UnaryOperator) -> UnaryOperator {
        let operator = self.token().expect("Failed to get token");
        let kind = &operator.kind();
        let op = op_matcher(kind);
        self.consume_token();
        op
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
            // If it is, enter panic mode.
            if self.go_into_panic_mode() {
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

    fn go_into_panic_mode(&mut self) -> bool {
        if !self.error {
            return false;
        }

        println!("PANIC PANIC PANIC!");
        // Consume tokens until we find a synchronizing token.
        while let Some(token) = self.token() {
            match token.kind() {
                TokenKind::Eof
                | TokenKind::Semicolon
                | TokenKind::IfKeyword
                | TokenKind::ByeKeyword
                | TokenKind::FUNcKeyword
                | TokenKind::ForKeyword
                | TokenKind::ElseKeyword
                | TokenKind::WhileKeyword
                | TokenKind::DoKeyword
                | TokenKind::LoopKeyword
                | TokenKind::BreakKeyword
                | TokenKind::ContinueKeyword
                | TokenKind::CaseKeyword
                | TokenKind::SwitchKeyword => break,
                TokenKind::CloseBrace => {
                    break;
                }
                _ => {
                    self.consume_token();
                    continue;
                }
            }
        }
        self.consume_token();
        self.error = false;

        return true;
    }

    fn add_error(&mut self, error_message: &str) {
        self.error_diag
            .borrow_mut()
            .expected_something_error(error_message, self.token_offset(-1));
    }

    fn is_at_end(&self) -> bool {
        if let Some(token) = self.token() {
            return token.kind() == TokenKind::Eof;
        }
        self.curr_token_index == self.tokens.len()
    }

    pub fn parse(&mut self) -> TranslationUnit {
        self.translation_unit()
    }

    fn translation_unit(&mut self) -> TranslationUnit {
        let mut functions = Vec::<Function>::new();
        let mut variables = Vec::<Statement>::new();
        loop {
            if self.matches_token_kind(TokenKind::FUNcKeyword) {
                match self.function() {
                    Some(function) => functions.push(function),
                    None => {}
                }
            } else if self.matches_data_type() {
                match self.var_decl() {
                    Some(var_decl) => variables.push(var_decl),
                    None => {}
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
            } else {
                panic!("Something unexpected happened :( (compiler error)")
            }
        }
        TranslationUnit::TranslationUnit {
            functions,
            variables,
        }
    }

    fn function(&mut self) -> Option<Function> {
        let position = self.position;
        self.expect(TokenKind::FUNcKeyword)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let parameters = self.params()?;
        self.expect(TokenKind::Arrow)?;
        let return_type = self.data_type()?;
        let block = self.block()?;

        Some(Function::Function {
            position,
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
        while !self.matches_token_kind(TokenKind::CloseParen) {
            self.expect(TokenKind::Comma)?;
            parameters.push(self.parameter()?);
        }
        self.expect(TokenKind::CloseParen)?;

        Some(parameters)
    }

    fn parameter(&mut self) -> Option<Parameter> {
        let position = self.position;
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Colon)?;
        let data_type = self.data_type()?;
        Some(Parameter::Parameter {
            position,
            identifier,
            data_type,
        })
    }

    fn block(&mut self) -> Option<Block> {
        let position = self.position;
        self.expect(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement>::new();

        while !self.matches_token_kind(TokenKind::CloseBrace) {
            match self.statement() {
                Some(statement) => statements.push(statement),
                None => {}
            }
        }
        self.expect(TokenKind::CloseBrace)?;

        Some(Block::Block {
            position,
            statements,
        })
    }

    fn statement(&mut self) -> Option<Statement> {
        let position = self.position;
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
                        position,
                        expression,
                        statement: Box::new(statement),
                        else_statement: Box::new(else_statement),
                    })
                } else {
                    Some(Statement::IfStatement {
                        position,
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
                        position,
                        ident: ident_expression,
                        length_expression: expression,
                        statement: Box::new(statement),
                    });
                }

                return Some(Statement::ForStatement {
                    position,
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
                    position,
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
                    position,
                    block,
                    expression,
                });
            }
            TokenKind::LoopKeyword => {
                self.expect(TokenKind::LoopKeyword)?;
                let block = self.block()?;
                return Some(Statement::LoopStatement {
                    position,
                    block: Box::new(block),
                });
            }
            TokenKind::BreakKeyword => {
                self.expect(TokenKind::BreakKeyword)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::BreakStatement { position });
            }
            TokenKind::ContinueKeyword => {
                self.expect(TokenKind::ContinueKeyword)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::ContinueStatement { position });
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
                        position,
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
                    position,
                    expression,
                    cases,
                });
            }
            TokenKind::ByeKeyword => {
                self.expect(TokenKind::ByeKeyword)?;
                let expression = self.expr()?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::ReturnStatement {
                    position,
                    expression,
                });
            }
            TokenKind::Semicolon => {
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::EmptyStatement { position });
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
                    position,
                    expression,
                });
            }
            TokenKind::OpenBrace => {
                let block = self.block()?;
                return Some(Statement::BlockStatement {
                    position,
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
                self.add_error("statement");
                self.error = true;
                self.go_into_panic_mode();
                return None;
            }
        };
    }

    fn case(&mut self) -> Option<Case> {
        self.expect(TokenKind::CaseKeyword)?;
        let expression = self.expr()?;
        let block = self.block()?;
        Some(Case::Case {
            expression,
            block: Box::new(block),
        })
    }

    fn var_decl(&mut self) -> Option<Statement> {
        let position = self.position;
        let data_type = self.data_type()?;
        self.expect(TokenKind::Arrow)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let statement = if self.matches_token_kind(TokenKind::Equal) {
            self.expect(TokenKind::Equal);
            let expression = self.expr()?;
            Statement::VariableDeclarationAndAssignment {
                position,
                identifier,
                data_type,
                expression,
            }
        } else {
            Statement::VariableDeclaration {
                position,
                identifier,
                data_type,
            }
        };

        self.expect(TokenKind::Semicolon)?;
        Some(statement)
    }

    fn matches_data_type(&self) -> bool {
        if let Some(token) = self.token() {
            return match token.kind() {
                TokenKind::XxlppKeyword
                | TokenKind::PpKeyword
                | TokenKind::SppKeyword
                | TokenKind::XsppKeyword
                | TokenKind::PKeyword
                | TokenKind::NoppKeyword
                | TokenKind::BoobaKeyword
                | TokenKind::YarnKeyword => true,
                _ => false,
            };
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
        let position = self.position;
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
                position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn comp(&mut self) -> Option<Expression> {
        let position = self.position;
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
                position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn term(&mut self) -> Option<Expression> {
        let position = self.position;
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
                position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn factor(&mut self) -> Option<Expression> {
        let position = self.position;
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
                position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }
        Some(expr)
    }

    fn unary(&mut self) -> Option<Expression> {
        let position = self.position;
        return if self.matches_token_kind(TokenKind::Bang)
            || self.matches_token_kind(TokenKind::Dash)
        {
            let op = match self.token()?.kind() {
                TokenKind::Bang => UnaryOperator::Not,
                TokenKind::Dash => UnaryOperator::Negate,
                _ => unreachable!(),
            };
            self.consume_token();
            let operand = self.unary()?;
            Some(Expression::UnaryExpression {
                position,
                op,
                operand: Box::new(operand),
            })
        } else {
            self.primary()
        };
    }

    fn primary(&mut self) -> Option<Expression> {
        let position = self.position;
        return match self.token()?.kind() {
            TokenKind::Identifier => {
                let identifier = self.expect(TokenKind::Identifier)?;
                return match self.token()?.kind() {
                    TokenKind::OpenParen => {
                        let arguments = self.args()?;
                        Some(Expression::FunctionCall {
                            position,
                            identifier,
                            arguments,
                        })
                    }
                    TokenKind::Equal => {
                        self.expect(TokenKind::Equal)?;
                        let expression = self.expr()?;
                        Some(Expression::AssignmentExpression {
                            position,
                            identifier,
                            expression: Box::new(expression),
                        })
                    }
                    _ => Some(Expression::IdentifierExpression {
                        position,
                        identifier,
                    }),
                };
            }
            TokenKind::YemKeyword => {
                self.expect(TokenKind::YemKeyword)?;
                Some(Expression::BoobaExpression {
                    position,
                    booba: true,
                })
            }
            TokenKind::NomKeyword => {
                self.expect(TokenKind::NomKeyword)?;
                Some(Expression::BoobaExpression {
                    position,
                    booba: false,
                })
            }
            TokenKind::Number => {
                let number = self.expect(TokenKind::Number)?;
                Some(Expression::PpExpression {
                    position,
                    pp: number.parse::<i32>().unwrap(),
                })
            }
            TokenKind::Yarn => {
                let yarn = self.expect(TokenKind::Yarn)?;
                Some(Expression::YarnExpression { position, yarn })
            }
            TokenKind::OpenParen => {
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;
                Some(expression)
            }
            _ => {
                self.add_error("expression");
                None
            }
        };
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
