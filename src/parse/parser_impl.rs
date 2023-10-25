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
use std::rc::Rc;

use crate::parse::error_diagnosis::{ErrorDiagnosis, SyntaxError};
use crate::parse::lexer::{Token, TokenKind};
use crate::parse::parser::{
    BinaryOperator, Case, DataType, Number, Statement, TranslationUnit, UnaryOperator,
};
use crate::parse::{Block, Expression, Function, Parser, Variable};

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

    pub fn parse(&mut self) -> Result<TranslationUnit<'a>, SyntaxError> {
        let translation_unit = self.translation_unit();
        self.error_diag.borrow().check_errors()?;

        Ok(translation_unit)
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

        Some(Function::new(
            position,
            identifier,
            return_type,
            parameters,
            block,
        ))
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
        Some(Variable::new(position, identifier, data_type, None, true))
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
        let token = self.token()?;
        let token_kind = token.kind();

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
                dbg!(&ident_expression);
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
            | TokenKind::OpenParen => {
                let expression = self.expr()?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Expression {
                    position: self.position,
                    expression,
                });
            }
            TokenKind::Identifier => {
                // Identifier can also be an expression. Need to look ahead,
                // if present, then it's assignment. If not, it's expression.
                return if self.token_offset(1)?.kind() == TokenKind::Equal {
                    let identifier = self.expect(TokenKind::Identifier)?;
                    self.expect(TokenKind::Equal)?;
                    let expression = self.expr()?;
                    Some(Statement::Assignment {
                        position: self.position,
                        identifier,
                        expression,
                    })
                } else {
                    let expression = self.expr()?;
                    self.expect(TokenKind::Semicolon)?;
                    Some(Statement::Expression {
                        position: self.position,
                        expression,
                    })
                };
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
                self.error_diag.borrow_mut().unexpected_token_error(token);
                self.add_error("statement");
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
        Some(Case::new(expression, Box::new(block)))
    }

    fn var_decl(&mut self) -> Option<Statement<'a>> {
        let data_type = self.data_type()?;
        self.expect(TokenKind::Arrow)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let statement = if self.matches_token_kind(TokenKind::Equal) {
            self.expect(TokenKind::Equal);
            let expression = self.expr()?;
            Statement::VariableDeclaration {
                variable: Variable::new(
                    self.position,
                    identifier,
                    data_type,
                    Some(expression),
                    false,
                ),
            }
        } else {
            Statement::VariableDeclaration {
                variable: Variable::new(self.position, identifier, data_type, None, false),
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
                let position = self.position;
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
                    _ => Some(Expression::Identifier {
                        position,
                        identifier,
                    }),
                }
            }
            TokenKind::YemKeyword => {
                let position = self.position;
                self.expect(TokenKind::YemKeyword)?;
                Some(Expression::Booba {
                    position,
                    value: true,
                })
            }
            TokenKind::NomKeyword => {
                let position = self.position;
                self.expect(TokenKind::NomKeyword)?;
                Some(Expression::Booba {
                    position,
                    value: false,
                })
            }
            TokenKind::Number => {
                let position = self.position;
                let number = self.expect(TokenKind::Number)?;
                if let Ok(value) = number.parse::<i32>() {
                    Some(Expression::Number {
                        position,
                        number_type: Number::Pp,
                        value,
                    })
                } else {
                    panic!("Invalid number")
                }
            }
            TokenKind::P => {
                let position = self.position;
                let char = self.expect(TokenKind::P)?;
                if let Some(value) = char.chars().next() {
                    Some(Expression::P { position, value })
                } else {
                    panic!("Invalid character")
                }
            }
            TokenKind::Yarn => {
                let position = self.position;
                let yarn = self.expect(TokenKind::Yarn)?;
                Some(Expression::Yarn {
                    position,
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
