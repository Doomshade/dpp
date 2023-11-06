//! This module contains the implementation of the parser. The parser is implemented using a
//! recursive descent parser. The grammar is defined in `grammar.pdf`. The parser is
//! implemented using the following rules:
//! ```
//! translation_unit -> (function | var_decl)*
//! function -> "func" identifier "(" params ")" "->" data_type block
//! params -> (param ("," param)*)?
//! param -> identifier ":" data_type
//! block -> "{" (statement)* "}"
//! stat -> if | for | while | do_while | loop | break | continue | switch | bye | print | ";"
//! if -> "if" "(" expr ")" statement ("else" statement)?
//! for -> "for" "(" identifier "=" expr "to" expr ")" statement
//! while -> "while" "(" expr ")" statement
//! do_while -> "do" block "while" "(" expr ")" ";"
//! loop -> "loop" block
//! break -> "break" ";"
//! continue -> "continue" ";"
//! switch -> "switch" "(" expr ")" "{" (case ("," case)*)? "}"
//! case -> "case" expr block
//! bye -> "bye" expr? ";"
//! print -> ("pprintln" | "pprint") "(" expr ")" ";"
//! expr -> equ
//! equ -> comp (("!=" | "==") comp)*
//! comp -> term ((">" | ">=" | "<" | "<=" | "||" | "&&") term)*
//! term -> factor (("+" | "-") factor)*
//! factor -> unary (("/" | "*") unary)*
//! unary -> ("!" | "-") unary | primary
//! primary -> identifier | "yem" | "nom" | number | "p" | yarn | "(" expr ")"
//! identifier -> identifier
//! number -> number
//! yarn -> yarn
//! ```
//! For each declaration in grammar we declare either an enum or a struct and a function that
//! parses the grammar construct.
//!
//! Each function returns an `Option<T>` where `T` is the type of the grammar construct. Each
//! function name starts with _ to indicate that it is a rewrite function. If the function returns
//! `None` it means that the function did not accept the current token in the current state. This
//! means that the parser should try to parse the current token with another function or handle
//! the error.

use crate::parse::error_diagnosis::SyntaxError;
use crate::parse::lexer::{LiteralKind, TokenKind};
use crate::parse::parser::{
    BinaryOperator, Case, DataType, LiteralValue, Modifier, Statement, TranslationUnit,
    UnaryOperator,
};
use crate::parse::{Block, Expression, Function, Parser, Variable};

impl<'a, 'b> Parser<'a, 'b> {
    /// # Summary
    /// Parses the input and returns a `TranslationUnit` if successful.
    ///
    /// # Errors
    /// Returns a `SyntaxError` if the input is invalid.
    ///
    /// # Examples
    /// ```
    /// use dpp::parse::Parser;
    /// use dpp::parse::lexer::Lexer;
    ///
    /// let input = "func main() -> pp { bye; }";
    /// let mut lexer = Lexer::new(input);
    /// let tokens = lexer.lex().unwrap();
    /// let mut parser = Parser::new("main.dpp", input, tokens);
    /// let translation_unit = parser.parse().unwrap();
    /// ```
    ///
    /// # Returns
    /// A `TranslationUnit` if successful.
    pub fn parse(mut self) -> Result<TranslationUnit<'a>, SyntaxError> {
        let translation_unit = self._transl_unit();
        self.error_diag.borrow().check_errors()?;

        Ok(translation_unit)
    }

    fn _transl_unit(&mut self) -> TranslationUnit<'a> {
        let mut functions = Vec::<Function<'a>>::new();
        let mut variable_declarations = Vec::<Statement<'a>>::new();
        loop {
            if self.matches_token_kind(TokenKind::FUNcKeyword) {
                if let Some(function) = self._function() {
                    functions.push(function);
                }
            } else if self.matches_data_type() || self.matches_modifier() {
                if let Some(var_decl) = self._var_decl() {
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

    fn _function(&mut self) -> Option<Function<'a>> {
        let position = self.position;

        self.expect(TokenKind::FUNcKeyword)?;
        let identifier = self.expect(TokenKind::Identifier)?;
        let parameters = self._params()?;
        self.expect(TokenKind::Arrow)?;
        let return_type = self._data_type()?;
        self.expect(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement<'a>>::new();
        while !self.matches_token_kind(TokenKind::CloseBrace)
            && !self.matches_token_kind(TokenKind::Eof)
        {
            if let Some(statement) = self._stat() {
                statements.push(statement);
            }
        }
        self.expect(TokenKind::CloseBrace)?;

        Some(Function::new(
            position,
            identifier,
            return_type,
            parameters,
            statements,
        ))
    }

    fn _params(&mut self) -> Option<Vec<Variable<'a>>> {
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

        let parameter = self._param()?;
        parameters.push(parameter);

        let mut invalid_params = false;
        while !self.matches_token_kind(TokenKind::CloseParen)
            && !self.matches_token_kind(TokenKind::Eof)
        {
            if invalid_params {
                self.add_error("parameter");
                self.consume_token();
            } else {
                invalid_params = invalid_params || self.expect(TokenKind::Comma).is_none();
                if !invalid_params {
                    let parameter = self._param();
                    invalid_params = invalid_params || parameter.is_none();
                    parameters.push(parameter?);
                }
            }
        }
        self.expect(TokenKind::CloseParen)?;

        Some(parameters)
    }

    fn _param(&mut self) -> Option<Variable<'a>> {
        let position = self.position;
        let modifiers = self._modifiers();
        let data_type = self._data_type()?;
        self.expect(TokenKind::Arrow)?;
        let identifier = self.expect(TokenKind::Identifier)?;
        Some(Variable::new(
            position, identifier, data_type, modifiers, None,
        ))
    }

    fn _block(&mut self) -> Option<Block<'a>> {
        let position = self.position;
        self.expect(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement<'a>>::new();

        while !self.matches_token_kind(TokenKind::CloseBrace)
            && !self.matches_token_kind(TokenKind::Eof)
        {
            if let Some(statement) = self._stat() {
                statements.push(statement);
            }
        }
        self.expect(TokenKind::CloseBrace)?;

        Some(Block::new(position, statements))
    }

    fn _stat(&mut self) -> Option<Statement<'a>> {
        let token = self.token()?;

        match token.kind() {
            TokenKind::IfKeyword => self._if(),
            TokenKind::ForKeyword => self._for(),
            TokenKind::WhileKeyword => self._while(),
            TokenKind::DoKeyword => self._do_while(),
            TokenKind::LoopKeyword => self._loop(),
            TokenKind::BreakKeyword => self._break(),
            TokenKind::ContinueKeyword => self._continue(),
            TokenKind::SwitchKeyword => self._switch(),
            TokenKind::ByeKeyword => self._bye(),
            TokenKind::PprintKeyword => self._pprint(),
            TokenKind::PprintlnKeyword => self._pprintln(),
            TokenKind::Semicolon => self._empty(),
            TokenKind::YemKeyword
            | TokenKind::NomKeyword
            | TokenKind::Literal(_)
            | TokenKind::OpenParen => self._expr_stat(),
            TokenKind::Identifier => {
                // Identifier can also be an expression. Need to look ahead,
                // if present, then it's assignment. If not, it's expression.
                if self.token_offset(1)?.kind() == TokenKind::Equal {
                    self._assign()
                } else {
                    self._expr_stat()
                }
            }
            TokenKind::OpenBrace => self._block_stat(),
            TokenKind::PpKeyword
            | TokenKind::PKeyword
            | TokenKind::FlaccidKeyword
            | TokenKind::ABKeyword
            | TokenKind::BoobaKeyword
            | TokenKind::YarnKeyword
            | TokenKind::ConstKeyword => self._var_decl(),
            _ => {
                self.error_diag.borrow_mut().unexpected_token_error(token);
                self.add_error("statement");
                self.error = true;
                self.go_into_panic_mode();
                self._stat()
            }
        }
    }

    fn _if(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::IfKeyword)?;
        self.expect(TokenKind::OpenParen)?;
        let expression = self._expr()?;
        self.expect(TokenKind::CloseParen)?;

        let statement = self._stat()?;
        if self.matches_token_kind(TokenKind::ElseKeyword) {
            self.expect(TokenKind::ElseKeyword)?;
            let else_statement = self._stat()?;
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

    fn _for(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::ForKeyword)?;
        self.expect(TokenKind::OpenParen)?;
        let index_ident = self.expect(TokenKind::Identifier)?;
        let ident_expression = if self.matches_token_kind(TokenKind::Equal) {
            self.expect(TokenKind::Equal)?;
            Some(self._expr()?)
        } else {
            None
        };
        self.expect(TokenKind::ToKeyword)?;
        let length_expression = self._expr()?;
        self.expect(TokenKind::CloseParen)?;
        let statement = self._stat()?;

        Some(Statement::For {
            position,
            index_ident,
            ident_expression,
            length_expression,
            statement: Box::new(statement),
        })
    }

    fn _while(&mut self) -> Option<Statement<'a>> {
        let position = self.position;

        self.expect(TokenKind::WhileKeyword)?;
        self.expect(TokenKind::OpenParen)?;
        let expression = self._expr()?;
        self.expect(TokenKind::CloseParen)?;
        let statement = self._stat()?;

        Some(Statement::While {
            position,
            expression,
            statement: Box::new(statement),
        })
    }

    fn _do_while(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::DoKeyword)?;
        let statement = self._stat()?;
        self.expect(TokenKind::WhileKeyword)?;
        self.expect(TokenKind::OpenParen)?;
        let expression = self._expr()?;
        self.expect(TokenKind::CloseParen)?;
        self.expect(TokenKind::Semicolon)?;
        Some(Statement::DoWhile {
            position,
            statement: Box::new(statement),
            expression,
        })
    }

    fn _loop(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::LoopKeyword)?;
        let block = self._stat()?;
        Some(Statement::Loop {
            position,
            statement: Box::new(block),
        })
    }

    fn _break(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::BreakKeyword)?;
        self.expect(TokenKind::Semicolon)?;
        Some(Statement::Break { position })
    }

    fn _continue(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::ContinueKeyword)?;
        self.expect(TokenKind::Semicolon)?;
        Some(Statement::Continue { position })
    }

    fn _switch(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::SwitchKeyword)?;
        self.expect(TokenKind::OpenParen)?;
        let expression = self._expr()?;
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

        cases.push(self._case()?);
        while !self.matches_token_kind(TokenKind::CloseBrace) {
            self.expect(TokenKind::Comma);
            cases.push(self._case()?);
        }

        self.expect(TokenKind::CloseBrace)?;
        Some(Statement::Switch {
            position,
            expression,
            cases,
        })
    }

    fn _case(&mut self) -> Option<Case<'a>> {
        let position = self.position;
        self.expect(TokenKind::CaseKeyword)?;
        let expression = self._expr()?;
        let block = self._block()?;
        Some(Case::new(position, expression, Box::new(block)))
    }

    fn _bye(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::ByeKeyword)?;
        if let Some(expression) = self._expr() {
            let ret = Statement::Bye {
                position,
                expression: Some(expression),
            };
            self.expect(TokenKind::Semicolon)?;
            return Some(ret);
        }

        self.expect(TokenKind::Semicolon)?;
        Some(Statement::Bye {
            position,
            expression: None,
        })
    }

    fn _pprint(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::PprintKeyword)?;
        self.expect(TokenKind::OpenParen)?;
        let expression = self._expr()?;
        self.expect(TokenKind::CloseParen)?;
        self.expect(TokenKind::Semicolon)?;

        Some(Statement::Print {
            position,
            print_function: Self::print,
            expression,
        })
    }

    fn _pprintln(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::PprintlnKeyword)?;
        self.expect(TokenKind::OpenParen)?;
        let expression = self._expr()?;
        self.expect(TokenKind::CloseParen)?;
        self.expect(TokenKind::Semicolon)?;

        Some(Statement::Print {
            position,
            print_function: Self::println,
            expression,
        })
    }

    fn _empty(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        self.expect(TokenKind::Semicolon)?;
        Some(Statement::Empty { position })
    }

    fn _assign(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        let identifier = self.expect(TokenKind::Identifier)?;
        self.expect(TokenKind::Equal)?;
        let expression = self._expr()?;
        self.expect(TokenKind::Semicolon)?;
        Some(Statement::Assignment {
            position,
            identifier,
            expression,
        })
    }

    fn _var_decl(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        let modifiers = self._modifiers();
        let data_type = self._data_type()?;
        self.expect(TokenKind::Arrow)?;

        let identifier = self.expect(TokenKind::Identifier)?;
        let statement = if self.matches_token_kind(TokenKind::Equal) {
            self.expect(TokenKind::Equal);
            let expression = self._expr()?;
            Statement::VariableDeclaration {
                position,
                variable: Variable::new(
                    self.position,
                    identifier,
                    data_type,
                    modifiers,
                    Some(expression),
                ),
            }
        } else {
            Statement::VariableDeclaration {
                position,
                variable: Variable::new(self.position, identifier, data_type, modifiers, None),
            }
        };

        self.expect(TokenKind::Semicolon)?;
        Some(statement)
    }

    fn _block_stat(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        let block = self._block()?;
        Some(Statement::Block {
            position,
            block: Box::new(block),
        })
    }

    fn _expr_stat(&mut self) -> Option<Statement<'a>> {
        let position = self.position;
        let expression = self._expr()?;
        self.expect(TokenKind::Semicolon)?;
        Some(Statement::Expression {
            position,
            expression,
        })
    }

    fn _data_type(&mut self) -> Option<DataType> {
        let token = self.expect_one_from(&[
            TokenKind::PpKeyword,
            TokenKind::FlaccidKeyword,
            TokenKind::ABKeyword,
            TokenKind::PKeyword,
            TokenKind::NoppKeyword,
            TokenKind::BoobaKeyword,
            TokenKind::YarnKeyword,
        ])?;

        match token.1 {
            TokenKind::PpKeyword => Some(DataType::Pp),
            TokenKind::FlaccidKeyword => Some(DataType::Flaccid),
            TokenKind::ABKeyword => Some(DataType::AB),
            TokenKind::PKeyword => Some(DataType::P),
            TokenKind::NoppKeyword => Some(DataType::Nopp),
            TokenKind::BoobaKeyword => Some(DataType::Booba),
            TokenKind::YarnKeyword => Some(DataType::Yarn),
            _ => None,
        }
    }

    fn _modifiers(&mut self) -> Vec<Modifier> {
        let mut modifiers = Vec::new();
        while let Some(modifier) = self._modifier() {
            self.consume_token();
            modifiers.push(modifier);
        }
        modifiers
    }

    fn _modifier(&mut self) -> Option<Modifier> {
        match self.token()?.kind() {
            TokenKind::ConstKeyword => Some(Modifier::Const),
            _ => None,
        }
    }

    fn _expr(&mut self) -> Option<Expression<'a>> {
        self._equ()
    }

    fn _equ(&mut self) -> Option<Expression<'a>> {
        let mut expr = self._comp()?;

        while self.matches_token_kind(TokenKind::BangEqual)
            || self.matches_token_kind(TokenKind::EqualEqual)
        {
            let op = match self.token()?.kind() {
                TokenKind::BangEqual => BinaryOperator::NotEqual,
                TokenKind::EqualEqual => BinaryOperator::Equal,
                _ => unreachable!(),
            };
            self.consume_token();

            let rhs = self._comp()?;
            expr = Expression::Binary {
                position: self.position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn _comp(&mut self) -> Option<Expression<'a>> {
        let mut expr = self._term()?;

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
            let rhs = self._term()?;

            expr = Expression::Binary {
                position: self.position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn _term(&mut self) -> Option<Expression<'a>> {
        let mut expr = self._factor()?;

        while self.matches_token_kind(TokenKind::Dash) || self.matches_token_kind(TokenKind::Plus) {
            let op = match self.token()?.kind() {
                TokenKind::Dash => BinaryOperator::Subtract,
                TokenKind::Plus => BinaryOperator::Add,
                _ => unreachable!(),
            };
            self.consume_token();
            let rhs = self._factor()?;

            expr = Expression::Binary {
                position: self.position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Some(expr)
    }

    fn _factor(&mut self) -> Option<Expression<'a>> {
        let mut expr = self._unary()?;

        while self.matches_token_kind(TokenKind::ForwardSlash)
            || self.matches_token_kind(TokenKind::Star)
        {
            let op = match self.token()?.kind() {
                TokenKind::ForwardSlash => BinaryOperator::Divide,
                TokenKind::Star => BinaryOperator::Multiply,
                _ => unreachable!(),
            };
            self.consume_token();
            let rhs = self._unary()?;
            expr = Expression::Binary {
                position: self.position,
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }
        Some(expr)
    }

    fn _unary(&mut self) -> Option<Expression<'a>> {
        if self.matches_token_kind(TokenKind::Bang) || self.matches_token_kind(TokenKind::Dash) {
            let op = match self.token()?.kind() {
                TokenKind::Bang => UnaryOperator::Not,
                TokenKind::Dash => UnaryOperator::Negate,
                _ => unreachable!(),
            };
            self.consume_token();
            let operand = self._unary()?;
            Some(Expression::Unary {
                position: self.position,
                op,
                operand: Box::new(operand),
            })
        } else {
            self._primary()
        }
    }

    fn _primary(&mut self) -> Option<Expression<'a>> {
        let token_kind = self.token()?.kind();
        match token_kind {
            TokenKind::Identifier => {
                let position = self.position;
                let identifier = self.expect(TokenKind::Identifier)?;
                match self.token()?.kind() {
                    TokenKind::OpenParen => {
                        let arguments = self._args()?;
                        Some(Expression::FunctionCall {
                            position,
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
                Some(Expression::Literal {
                    position,
                    value: LiteralValue::Booba(true),
                })
            }
            TokenKind::NomKeyword => {
                let position = self.position;
                self.expect(TokenKind::NomKeyword)?;
                Some(Expression::Literal {
                    position,
                    value: LiteralValue::Booba(false),
                })
            }
            TokenKind::Literal(literal_kind) => {
                let position = self.position;
                let literal = self.expect(token_kind)?;
                match literal_kind {
                    LiteralKind::Pp => {
                        if let Ok(value) = literal.parse::<i32>() {
                            Some(Expression::Literal {
                                position,
                                value: LiteralValue::Pp(value),
                            })
                        } else {
                            panic!("Invalid number")
                        }
                    }
                    LiteralKind::P => {
                        if let Some(value) = literal.chars().next() {
                            Some(Expression::Literal {
                                position,
                                value: LiteralValue::P(value),
                            })
                        } else {
                            panic!("Invalid character")
                        }
                    }
                    LiteralKind::Yarn => Some(Expression::Literal {
                        position,
                        value: LiteralValue::Yarn(literal),
                    }),
                    _ => todo!("Not yet implemented"),
                }
            }
            TokenKind::OpenParen => {
                self.expect(TokenKind::OpenParen)?;
                let expression = self._expr()?;
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

    fn _args(&mut self) -> Option<Vec<Expression<'a>>> {
        self.expect(TokenKind::OpenParen)?;
        let mut args = Vec::<Expression<'a>>::new();

        if self.matches_token_kind(TokenKind::CloseParen) {
            self.expect(TokenKind::CloseParen)?;
            return Some(args);
        }

        let arg = self._expr()?;
        args.push(arg);
        while !self.matches_token_kind(TokenKind::CloseParen)
            && !self.matches_token_kind(TokenKind::Eof)
        {
            self.expect(TokenKind::Comma)?;
            args.push(self._expr()?);
        }
        self.expect(TokenKind::CloseParen)?;
        Some(args)
    }
}
