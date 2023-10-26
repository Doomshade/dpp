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

use crate::parse::error_diagnosis::SyntaxError;
use crate::parse::lexer::TokenKind;
use crate::parse::parser::{
    BinaryOperator, Case, DataType, NumberType, Statement, TranslationUnit, UnaryOperator,
};
use crate::parse::{Block, Expression, Function, Parser, Variable};

impl<'a, 'b> Parser<'a, 'b> {
    pub fn parse(mut self) -> Result<TranslationUnit<'a>, SyntaxError> {
        let translation_unit = self.transl_unit();
        self.error_diag.borrow().check_errors()?;

        Ok(translation_unit)
    }

    fn transl_unit(&mut self) -> TranslationUnit<'a> {
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

        let parameter = self.param()?;
        parameters.push(parameter);

        let mut invalid_params = false;
        while !self.matches_token_kind(TokenKind::CloseParen) {
            if invalid_params {
                self.add_error("parameter");
                self.consume_token();
            } else {
                invalid_params = invalid_params || self.expect(TokenKind::Comma).is_none();
                if !invalid_params {
                    let parameter = self.param();
                    invalid_params = invalid_params || parameter.is_none();
                    parameters.push(parameter?);
                }
            }
        }
        self.expect(TokenKind::CloseParen)?;

        Some(parameters)
    }

    fn param(&mut self) -> Option<Variable<'a>> {
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
            if let Some(statement) = self.stat() {
                statements.push(statement);
            }
        }
        self.expect(TokenKind::CloseBrace)?;

        Some(Block::new(position, statements))
    }

    fn stat(&mut self) -> Option<Statement<'a>> {
        let token = self.token()?;
        let token_kind = token.kind();
        let position = self.position;

        return match token_kind {
            TokenKind::IfKeyword => {
                self.expect(TokenKind::IfKeyword)?;
                self.expect(TokenKind::OpenParen)?;
                let expression = self.expr()?;
                self.expect(TokenKind::CloseParen)?;

                let statement = self.stat()?;
                if self.matches_token_kind(TokenKind::ElseKeyword) {
                    self.expect(TokenKind::ElseKeyword)?;
                    let else_statement = self.stat()?;
                    Some(Statement::IfElse {
                        position,
                        expression,
                        statement: Box::new(statement),
                        else_statement: Box::new(else_statement),
                    })
                } else {
                    Some(Statement::If {
                        position,
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
                let statement = self.stat()?;

                return Some(Statement::For {
                    position,
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
                let statement = self.stat()?;

                return Some(Statement::While {
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
                return Some(Statement::DoWhile {
                    position,
                    block,
                    expression,
                });
            }
            TokenKind::LoopKeyword => {
                self.expect(TokenKind::LoopKeyword)?;
                let block = self.block()?;
                return Some(Statement::Loop {
                    position,
                    block: Box::new(block),
                });
            }
            TokenKind::BreakKeyword => {
                self.expect(TokenKind::BreakKeyword)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Break { position });
            }
            TokenKind::ContinueKeyword => {
                self.expect(TokenKind::ContinueKeyword)?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Continue { position });
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
                return Some(Statement::Switch {
                    position,
                    expression,
                    cases,
                });
            }
            TokenKind::ByeKeyword => {
                self.expect(TokenKind::ByeKeyword)?;
                if let Some(expression) = self.expr() {
                    let ret = Statement::Bye {
                        position,
                        expression: Some(expression),
                    };
                    self.expect(TokenKind::Semicolon)?;
                    return Some(ret);
                }

                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Bye {
                    position,
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
                    position,
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
                return Some(Statement::Empty { position });
            }
            TokenKind::YemKeyword
            | TokenKind::NomKeyword
            | TokenKind::NumberLiteral
            | TokenKind::YarnLiteral
            | TokenKind::OpenParen => {
                let expression = self.expr()?;
                self.expect(TokenKind::Semicolon)?;
                return Some(Statement::Expression {
                    position,
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
                    self.expect(TokenKind::Semicolon)?;
                    Some(Statement::Assignment {
                        position,
                        identifier,
                        expression,
                    })
                } else {
                    let expression = self.expr()?;
                    self.expect(TokenKind::Semicolon)?;
                    Some(Statement::Expression {
                        position,
                        expression,
                    })
                };
            }
            TokenKind::OpenBrace => {
                let block = self.block()?;
                return Some(Statement::Block {
                    position,
                    block: Box::new(block),
                });
            }
            TokenKind::XxlppKeyword
            | TokenKind::PpKeyword
            | TokenKind::SppKeyword
            | TokenKind::XsppKeyword
            | TokenKind::PKeyword
            | TokenKind::RatioKeyword
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
                return self.stat();
            }
        };
    }

    fn case(&mut self) -> Option<Case<'a>> {
        let position = self.position;
        self.expect(TokenKind::CaseKeyword)?;
        let expression = self.expr()?;
        let block = self.block()?;
        Some(Case::new(position, expression, Box::new(block)))
    }

    fn var_decl(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        let data_type = self.data_type()?;
        self.expect(TokenKind::Arrow)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let statement = if self.matches_token_kind(TokenKind::Equal) {
            self.expect(TokenKind::Equal);
            let expression = self.expr()?;
            Statement::VariableDeclaration {
                position,
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
                position,
                variable: Variable::new(self.position, identifier, data_type, None, false),
            }
        };

        self.expect(TokenKind::Semicolon)?;
        Some(statement)
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
            TokenKind::RatioKeyword,
        ])?;

        match token.1 {
            TokenKind::PpKeyword => Some(DataType::Number(NumberType::Pp)),
            TokenKind::PKeyword => Some(DataType::P),
            TokenKind::NoppKeyword => Some(DataType::Nopp),
            TokenKind::BoobaKeyword => Some(DataType::Booba),
            TokenKind::YarnKeyword => Some(DataType::Yarn),
            TokenKind::RatioKeyword => Some(DataType::Ratio),
            _ => None,
        }
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
            || self.matches_token_kind(TokenKind::PipePipe)
            || self.matches_token_kind(TokenKind::AmpersandAmpersand)
        {
            let op = match self.token()?.kind() {
                TokenKind::Greater => BinaryOperator::GreaterThan,
                TokenKind::GreaterEqual => BinaryOperator::GreaterThanOrEqual,
                TokenKind::Less => BinaryOperator::LessThan,
                TokenKind::LessEqual => BinaryOperator::LessThanOrEqual,
                TokenKind::PipePipe => BinaryOperator::Or,
                TokenKind::AmpersandAmpersand => BinaryOperator::And,
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
            TokenKind::NumberLiteral => {
                let position = self.position;
                let number = self.expect(TokenKind::NumberLiteral)?;
                if let Ok(value) = number.parse::<i32>() {
                    Some(Expression::Number {
                        position,
                        number_type: NumberType::Pp,
                        value,
                    })
                } else {
                    panic!("Invalid number")
                }
            }
            TokenKind::PLiteral => {
                let position = self.position;
                let char = self.expect(TokenKind::PLiteral)?;
                if let Some(value) = char.chars().next() {
                    Some(Expression::P { position, value })
                } else {
                    panic!("Invalid character")
                }
            }
            TokenKind::YarnLiteral => {
                let position = self.position;
                let yarn = self.expect(TokenKind::YarnLiteral)?;
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
                Some(Expression::Invalid {
                    position: self.position,
                })
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

    fn _struct_(&mut self) -> DataType<'a> {
        todo!()
    }
}
