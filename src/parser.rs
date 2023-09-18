use std::ops::Deref;
use crate::lexer::{Lexer, SyntaxError, Token, TokenKind};

pub struct Parser {
    lexer: Lexer,
    row: usize,
    col: usize,
    program: Option<Program>,
}

#[derive(Clone, Debug)]
pub struct Program {
    binary_expression: BinaryExpression,
}

impl Program {
    pub fn binary_expression(&self) -> &BinaryExpression {
        &self.binary_expression
    }
}

#[derive(Clone, Debug)]
pub struct Expression {
    pub num: i64,
}

#[derive(Clone, Debug)]
pub struct BinaryExpression {
    lhs: Box<Expression>,
    op: Op,
    rhs: Box<Expression>,
}

impl BinaryExpression {
    pub fn lhs(&self) -> &Box<Expression> {
        &self.lhs
    }
    pub fn op(&self) -> &Op {
        &self.op
    }

    pub fn rhs(&self) -> &Box<Expression> {
        &self.rhs
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Op {
    Add,
}

pub enum Punctuation {
    Semicolon,
}

impl Parser {
    pub const fn new(lexer: Lexer) -> Self {
        Self { lexer, row: 0, col: 0, program: None }
    }

    pub fn parse(&mut self) -> Result<Program, SyntaxError> {
        if self.program.is_some() {
            return Ok(self.program.as_mut().unwrap().to_owned());
        }
        self.lexer.reset();
        self.lexer.lex()?;
        self.parse_program()
    }

    pub fn print_parse_tree(&mut self) {
        let program = self.parse().expect("Failed to parse program");
        println!("{:#?}", program);
    }

    fn parse_program(&mut self) -> Result<Program, SyntaxError> {
        let binary_expression = self.parse_binary_expression()?;
        Ok(Program { binary_expression })
    }

    fn parse_binary_expression(&mut self) -> Result<BinaryExpression, SyntaxError> {
        let lhs = self.expect_expression()?;
        let op = self.expect_operator()?;
        let rhs = self.expect_expression()?;
        self.expect_punctuation(Punctuation::Semicolon)?;
        Ok(BinaryExpression { lhs: Box::new(lhs), op, rhs: Box::new(rhs) })
    }

    fn expect_punctuation(&mut self, punct: Punctuation) -> Result<(), SyntaxError> {
        let punct_value = match punct { Punctuation::Semicolon => { ';' } };
        self.expect_token(TokenKind::Punctuation, String::from(punct_value))?;
        self.lexer.consume_token();
        Ok(())
    }

    fn expect_token(&mut self, expected_token_kind: TokenKind, expected_value: String) -> Result<(), SyntaxError> {
        let token = self.lexer.token().unwrap_or_else(|| panic!("Expected {expected_value}"));
        if token.kind != expected_token_kind {
            return Err(SyntaxError {
                row: 0,
                col: 0,
                message: format!("Invalid token '{}', expected '{expected_value}'", token.value.as_ref().unwrap().as_str()),
            });
        }
        let value = token.value.as_ref().expect("Expected value");
        if value.eq(&expected_value) {
            Ok(())
        } else {
            Err(SyntaxError {
                row: 0,
                col: 0,
                message: format!("Expected {expected_value}"),
            })
        }
    }

    fn expect_expression(&mut self) -> Result<Expression, SyntaxError> {
        let num = self.expect_number()?;
        Ok(Expression { num })
    }

    fn expect_number(&mut self) -> Result<i64, SyntaxError> {
        let num_token = self.expect_token_kind(TokenKind::Number)?;
        let result = num_token.value.as_ref().expect("Expected value").parse::<i64>().map_err(|_| SyntaxError {
            row: 0,
            col: 0,
            message: String::new(),
        });
        self.lexer.consume_token();
        result
    }

    fn expect_operator(&mut self) -> Result<Op, SyntaxError> {
        let op_token = self.expect_token_kind(TokenKind::Operator)?;
        let result = match op_token.value.as_ref().expect("Expected value").as_str() {
            "+" => Ok(Op::Add),
            _ => Err(SyntaxError {
                row: 0,
                col: 0,
                message: String::new(),
            })
        };
        self.lexer.consume_token();
        result
    }

    fn expect_token_kind(&self, expected_token_kind: TokenKind) -> Result<&Token, SyntaxError> {
        let token = self.lexer.token().unwrap_or_else(|| panic!("Expected {expected_token_kind:?}"));
        if token.kind != expected_token_kind {
            return Err(SyntaxError {
                row: 0,
                col: 0,
                message: format!("Unexpected token kind '{token:?}'. Expected \
                '{expected_token_kind:?}'"),
            });
        }
        Ok(token)
    }
}
