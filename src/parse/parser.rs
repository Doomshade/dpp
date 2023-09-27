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

    /// Checks whether **the token** is accepted in the current state. If
    /// it does, returns the result of the function in Some and **consumes the token**. If it does
    /// not, returns None.
    ///
    /// The result of the function is either the value of the token or an empty string if the
    /// value is not present.
    /// # Arguments
    ///
    /// * `token_kind`: the token kind to accept
    ///
    /// returns: Option<String> the value of the token; is an empty string if it does not exist,
    /// or None if the token is not accepted
    ///
    /// # Examples
    ///
    /// ```
    /// if self.accepts(TokenKind::IfKeyword).is_some() {
    ///     (...)
    /// }
    ///
    /// // or
    /// if let Some(identifier) = self.accepts(TokenKind::Identifier) {
    ///    (...)
    /// }
    ///
    /// // or
    /// fn some_function(&mut self) -> Option<...> {
    ///     // If it is not accepted, return prematurely from the parsing function.
    ///     self.accepts(TokenKind::OpenParen)?;
    /// ```
    fn accepts(&mut self, token_kind: TokenKind) -> Option<String> {
        if let Some(token) = self.token() {
            if token.kind() == token_kind {
                let optional_token_value = token.value();
                self.consume_token();
                if let Some(token_value) = optional_token_value {
                    return Some(token_value);
                }
                return Some(String::new());
            }
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

    /// Check whether **the rewrite (grammar) function** accepts the input in the current state. If
    /// it does, returns the result of the function in Some. If it does not, returns None.
    ///
    /// The postfix *_* is added to the function name to distinguish between accepting a token
    /// and a rewrite (grammar) function.
    ///
    /// # Arguments
    ///
    /// * `grammar_func`: the grammar function to call
    ///
    /// returns: Option<T> the result of the call
    ///
    /// # Examples
    ///
    /// ```
    /// // Check if the current state accepts a function declaration.
    /// // If it does, push the function declaration to some vector.
    /// if let Some(function) = self.accepts_(Self::function) {
    ///      functions.push(function);
    ///  }
    /// ```
    fn accepts_<T: Default>(&mut self, grammar_func: fn(&mut Self) -> Option<T>) -> Option<T> {
        if let Some(ret_from_something) = grammar_func(self) {
            return Some(ret_from_something);
        }

        None
    }

    /// Expects **the rewrite (grammar) function** to accept the input in the current state. If
    /// it does, returns the result of the function. If it does not, returns the default
    /// value of the rewrite function result (usually *InvalidSomething*) and adds an error to the
    /// error diagnostics.
    ///
    /// The error message passed to diagnostics is in format "Expected: {error_message}".
    ///
    /// The postfix *_* is added to the function name to distinguish between accepting a token
    /// and a rewrite (grammar) function.
    /// # Arguments
    ///
    /// * `grammar_func`: the grammar function to call
    /// * `error_message`: the error message
    ///
    /// returns: Option<T> the result of the call
    ///
    /// # Examples
    ///
    /// ```
    /// // Expect a block in the current state.
    /// // Pass in the string "block" as the error message if the block is not present.
    /// // The error will be prefixed with "Expected: (...)".
    /// let block = self.expect_(Self::block, "block");
    /// ```
    fn expect_<T: Default>(
        &mut self,
        grammar_func: fn(&mut Self) -> Option<T>,
        error_message: &str,
    ) -> T {
        if let Some(ret_from_something) = grammar_func(self) {
            return ret_from_something;
        }

        self.add_error(error_message);
        T::default()
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
        self.error = false;

        return true;
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
        let mut variables = Vec::<Statement>::new();
        loop {
            if let Some(function) = self.accepts_(Self::function) {
                functions.push(function);
            } else if let Some(variable_declaration) = self.accepts_(Self::var_decl) {
                variables.push(variable_declaration);
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
        self.accepts(TokenKind::FUNcKeyword)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let parameters = self.params()?;
        self.expect(TokenKind::Arrow)?;
        let return_type = self.expect_(Self::data_type, "data type");
        let block = self.expect_(Self::block, "block");

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
        if self.accepts(TokenKind::CloseParen).is_some() {
            return Some(parameters);
        }

        let parameter = self.parameter()?;
        parameters.push(parameter);
        loop {
            if self.accepts(TokenKind::Comma).is_some() {
                parameters.push(self.parameter()?);
            } else if self.accepts(TokenKind::CloseParen).is_some() {
                break;
            } else {
                self.add_error("Expected \",\"");
                parameters.push(self.parameter()?);
            }
        }

        Some(parameters)
    }

    fn parameter(&mut self) -> Option<Parameter> {
        let position = self.position;
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Colon)?;
        let data_type = self.expect_(Self::data_type, "data type");
        Some(Parameter::Parameter {
            position,
            identifier,
            data_type,
        })
    }

    fn block(&mut self) -> Option<Block> {
        let position = self.position;
        self.accepts(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement>::new();

        while !self.matches_token_kind(TokenKind::CloseBrace) {
            statements.push(self.statement()?);
        }
        self.expect(TokenKind::CloseBrace)?;

        Some(Block::Block {
            position,
            statements,
        })
    }

    fn is_at_end(&self) -> bool {
        if let Some(token) = self.token() {
            return token.kind() == TokenKind::Eof;
        }
        self.curr_token_index == self.tokens.len()
    }

    fn statement(&mut self) -> Option<Statement> {
        let position = self.position;
        let token_kind = self.token()?.kind();

        return match token_kind {
            TokenKind::IfKeyword => {
                self.expect(TokenKind::IfKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expect_(Self::expr, "expression");
                self.expect(TokenKind::CloseParen)?;

                let statement = self.expect_(Self::statement, "statement");
                if self.matches_token_kind(TokenKind::ElseKeyword) {
                    self.expect(TokenKind::ElseKeyword)?;
                    let else_statement = self.expect_(Self::statement, "statement");
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
                    ident_expression = Some(self.expect_(Self::expr, "expression"));
                } else {
                    ident_expression = None;
                }
                self.expect(TokenKind::ToKeyword)?;
                let expression = self.expect_(Self::expr, "expression");
                self.expect(TokenKind::CloseParen)?;
                let statement = self.expect_(Self::statement, "statement");

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
                let expression = self.expect_(Self::expr, "expression");
                self.expect(TokenKind::CloseParen)?;
                let statement = self.expect_(Self::statement, "statement");

                return Some(Statement::WhileStatement {
                    position,
                    expression,
                    statement: Box::new(statement),
                });
            }
            TokenKind::DoKeyword => {
                self.expect(TokenKind::DoKeyword)?;
                let block = self.expect_(Self::block, "block");
                self.expect(TokenKind::WhileKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expect_(Self::expr, "expression");
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
                let block = self.expect_(Self::block, "block");
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
                let expression = self.expect_(Self::expr, "expression");
                self.expect(TokenKind::CloseParen)?;
                self.expect(TokenKind::OpenBrace)?;
                let mut cases = Vec::<Case>::new();
                while let Some(case) = self.case() {
                    cases.push(case);
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
                let expression = self.expect_(Self::expr, "expression");
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
                None
            }
        };
    }

    fn case(&mut self) -> Option<Case> {
        self.accepts(TokenKind::CaseKeyword)?;
        let expression = self.expect_(Self::expr, "expression");
        let block = self.expect_(Self::block, "block");
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
                | TokenKind::Yarn => true,
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
                TokenKind::Yarn => {
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
        let mut comparison = self.comp();

        while self.matches_token_kind(TokenKind::BangEqual)
            || self.matches_token_kind(TokenKind::EqualEqual)
        {
            let op = self.binop(|kind| match kind {
                TokenKind::BangEqual => BinaryOperator::NotEqual,
                TokenKind::EqualEqual => BinaryOperator::Equal,
                _ => unreachable!(),
            });

            let rhs = self.expect_(Self::comp, "expression");
            comparison.as_ref()?;
            if let Some(expression) = comparison {
                comparison = Some(Expression::BinaryExpression {
                    position,
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }

        comparison
    }

    fn comp(&mut self) -> Option<Expression> {
        let position = self.position;
        let mut term = self.term();

        while self.matches_token_kind(TokenKind::Greater)
            || self.matches_token_kind(TokenKind::GreaterEqual)
            || self.matches_token_kind(TokenKind::Less)
            || self.matches_token_kind(TokenKind::LessEqual)
        {
            let op = self.binop(|kind| match kind {
                TokenKind::Greater => BinaryOperator::GreaterThan,
                TokenKind::GreaterEqual => BinaryOperator::GreaterThanOrEqual,
                TokenKind::Less => BinaryOperator::LessThan,
                TokenKind::LessEqual => BinaryOperator::LessThanOrEqual,
                _ => unreachable!(),
            });
            let rhs = self.expect_(Self::term, "expression");
            if term.is_none() {
                self.add_error("expression");
            }

            let expression = term?;
            term = Some(Expression::BinaryExpression {
                position,
                lhs: Box::new(expression),
                op,
                rhs: Box::new(rhs),
            });
        }

        term
    }

    fn term(&mut self) -> Option<Expression> {
        let position = self.position;
        let mut factor = self.factor();

        while self.matches_token_kind(TokenKind::Dash) || self.matches_token_kind(TokenKind::Plus) {
            let op = self.binop(|kind| match kind {
                TokenKind::Dash => BinaryOperator::Subtract,
                TokenKind::Plus => BinaryOperator::Add,
                _ => unreachable!(),
            });
            let rhs = self.expect_(Self::factor, "expression");
            factor.as_ref()?;

            if let Some(expression) = factor {
                factor = Some(Expression::BinaryExpression {
                    position,
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }

        factor
    }

    fn factor(&mut self) -> Option<Expression> {
        let position = self.position;
        let mut unary = self.unary();

        while self.matches_token_kind(TokenKind::ForwardSlash)
            || self.matches_token_kind(TokenKind::Star)
        {
            let op = self.binop(|kind| match kind {
                TokenKind::ForwardSlash => BinaryOperator::Divide,
                TokenKind::Star => BinaryOperator::Multiply,
                _ => unreachable!(),
            });
            unary.as_ref()?;
            if let Some(expression) = unary {
                let rhs = self.expect_(Self::unary, "expression");
                unary = Some(Expression::BinaryExpression {
                    position,
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }
        unary
    }

    fn unary(&mut self) -> Option<Expression> {
        let position = self.position;
        if self.matches_token_kind(TokenKind::Bang) || self.matches_token_kind(TokenKind::Dash) {
            let op = self.unop(|kind| match kind {
                TokenKind::Bang => UnaryOperator::Not,
                TokenKind::Dash => UnaryOperator::Negate,
                _ => unreachable!(),
            });
            let operand = self.expect_(Self::unary, "expression");
            return Some(Expression::UnaryExpression {
                position,
                op,
                operand: Box::new(operand),
            });
        }

        self.primary()
    }

    fn primary(&mut self) -> Option<Expression> {
        let position = self.position;
        if let Some(identifier) = self.accepts(TokenKind::Identifier) {
            return if let Some(arguments) = self.args() {
                return Some(Expression::FunctionCall {
                    position,
                    identifier,
                    arguments,
                });
            } else if self.accepts(TokenKind::Equal).is_some() {
                let expression = self.expect_(Self::expr, "expression");
                Some(Expression::AssignmentExpression {
                    position,
                    identifier,
                    expression: Box::new(expression),
                })
            } else {
                Some(Expression::IdentifierExpression {
                    position,
                    identifier,
                })
            };
        } else if self.accepts(TokenKind::NomKeyword).is_some() {
            return Some(Expression::BoobaExpression {
                position,
                booba: false,
            });
        } else if self.accepts(TokenKind::YemKeyword).is_some() {
            return Some(Expression::BoobaExpression {
                position,
                booba: true,
            });
        } else if let Some(number) = self.accepts(TokenKind::Number) {
            return Some(Expression::PpExpression {
                position,
                pp: number.parse::<i32>().unwrap(),
            });
        } else if let Some(yarn) = self.accepts(TokenKind::Yarn) {
            return Some(Expression::YarnExpression { position, yarn });
        } else if self.accepts(TokenKind::OpenParen).is_some() {
            let expression = self.expect_(Self::expr, "expression");
            self.expect(TokenKind::CloseParen)?;
            return Some(expression);
        }

        None
    }

    fn args(&mut self) -> Option<Vec<Expression>> {
        self.accepts(TokenKind::OpenParen)?;
        let mut args = Vec::<Expression>::new();

        if self.accepts(TokenKind::CloseParen).is_some() {
            return Some(args);
        }
        // else if let Some(arg) = self.expr() {
        //     args.push(arg);
        //     loop {
        //         if self.accepts(TokenKind::Comma).is_some() {
        //             args.push(self.expect_(Self::expr, "expression"));
        //         } else if self.accepts(TokenKind::CloseParen).is_some() {
        //             break;
        //         }
        //     }
        // } else {
        //     self.expect(TokenKind::CloseParen)?;
        // }
        let arg = self.expect_(Self::expr, "expression");
        args.push(arg);
        loop {
            if self.accepts(TokenKind::Comma).is_some() {
                args.push(self.expect_(Self::expr, "expression"));
            } else if self.accepts(TokenKind::CloseParen).is_some() {
                break;
            } else {
                self.add_error("Expected \",\"");
                self.consume_token();
                args.push(self.expect_(Self::expr, "expression"));
            }
        }
        Some(args)
    }
}
