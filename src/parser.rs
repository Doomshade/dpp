use std::fmt;
use crate::lexer::{Lexer, SyntaxError, Token, TokenKind};

pub struct Parser {
    lexer: Lexer,
    row: usize,
    col: usize,
    program: Option<Program>,
}

#[derive(Clone)]
pub struct Program {
    expression: Option<Box<Expression>>,
}

impl Program {
    pub fn expression(&self) -> &Option<Box<Expression>> {
        &self.expression
    }
}

#[derive(Clone)]
pub struct Expression {
    num: Option<i64>,
    binary_expression: Option<Box<BinaryExpression>>,
}

impl Expression {
    pub fn num(&self) -> &Option<i64> {
        &self.num
    }

    pub fn binary_expression(&self) -> &Option<Box<BinaryExpression>> {
        &self.binary_expression
    }
}

#[derive(Clone)]
pub struct BinaryExpression {
    lhs: Box<Expression>,
    op: Op,
    rhs: Box<Expression>,
}

impl fmt::Debug for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Program")
         .field("expression", &self.expression)
         .finish()
    }
}

impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug_struct = f.debug_struct("Expression");
        if let Some(num) = &self.num {
            debug_struct.field("num", num);
        }
        if let Some(binary_expression) = &self.binary_expression {
            debug_struct.field("binary_expression", binary_expression);
        }
        debug_struct.finish()
    }
}

impl fmt::Debug for BinaryExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BinaryExpression")
         .field("lhs", &self.lhs)
         .field("op", &self.op)
         .field("rhs", &self.rhs)
         .finish()
    }
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
            return Ok(self.program.as_mut().unwrap().clone());
        }
        self.lexer.reset();
        self.lexer.lex()?;
        self.parse_program()
    }

    pub fn print_parse_tree(&mut self) {
        let program = self.parse().expect("Failed to parse program");
        println!("{program:#?}");
    }

    fn parse_program(&mut self) -> Result<Program, SyntaxError> {
        let expression = Some(Box::new(self.parse_expression()?));
        Ok(Program { expression })
    }

    fn parse_binary_expression(&mut self) -> Result<BinaryExpression, SyntaxError> {
        let lhs = self.parse_expression()?;
        let op = self.parse_operator()?;
        let rhs = self.parse_expression()?;
        Ok(BinaryExpression { lhs: Box::new(lhs), op, rhs: Box::new(rhs) })
    }

    fn parse_punctuation(&mut self, punct: Punctuation) -> Result<(), SyntaxError> {
        let punct_value = match punct { Punctuation::Semicolon => { ';' } };
        self.parse_token(TokenKind::Punctuation, String::from(punct_value))?;
        self.lexer.consume_token();
        Ok(())
    }

    fn parse_token(&mut self, expected_token_kind: TokenKind, expected_value: String) -> Result<(), SyntaxError> {
        let token = self.lexer.token().unwrap_or_else(|| panic!("Expected {expected_value}"));
        if token.kind != expected_token_kind {
            return Err(SyntaxError {
                file: file!().to_string(),
                row: line!() as usize,
                col: column!() as usize,
                message: format!("Invalid token '{}', expected '{expected_value}'", token.value.as_ref().unwrap().as_str()),
            });
        }
        let value = token.value.as_ref().expect("Expected value");
        if value.eq(&expected_value) {
            Ok(())
        } else {
            Err(SyntaxError {
                file: file!().to_string(),
                row: column!() as usize,
                col: line!() as usize,
                message: format!("Expected {expected_value}"),
            })
        }
    }

    fn parse_expression(&mut self) -> Result<Expression, SyntaxError> {
        let num = self.parse_number()?;

        let op_token = self.lexer.token();
        if op_token.is_some() && op_token.unwrap().kind == TokenKind::Operator {
            let lhs = Expression { num: Some(num), binary_expression: None };
            let op = self.parse_operator()?;
            let rhs = self.parse_expression()?;
            return Ok(Expression {
                num: None,
                binary_expression: Some(Box::new(BinaryExpression {
                    lhs: Box::new(lhs),
                    op,
                    rhs: Box::new(rhs),
                })),
            });
        }
        Ok(Expression { num: Some(num), binary_expression: None })
    }

    fn parse_number(&mut self) -> Result<i64, SyntaxError> {
        let num_token = self.parse_token_kind(TokenKind::Number)?;
        let result = num_token.value.as_ref().expect("Expected value").parse::<i64>().map_err(|_| SyntaxError {
            file: file!().to_string(),
            row: line!() as usize,
            col: column!() as usize,
            message: String::new(),
        });
        self.lexer.consume_token();
        result
    }

    fn parse_operator(&mut self) -> Result<Op, SyntaxError> {
        let op_token = self.parse_token_kind(TokenKind::Operator)?;
        let result = match op_token.value.as_ref().expect("Expected value").as_str() {
            "+" => Ok(Op::Add),
            _ => Err(SyntaxError {
                file: file!().to_string(),

                row: line!() as usize,
                col: column!() as usize,
                message: String::new(),
            })
        };
        self.lexer.consume_token();
        result
    }

    fn parse_token_kind(&self, expected_token_kind: TokenKind) -> Result<&Token, SyntaxError> {
        let token = self.lexer.token().unwrap_or_else(|| panic!("Expected {expected_token_kind:?}"));
        if token.kind != expected_token_kind {
            return Err(SyntaxError {
                file: file!().to_string(),
                row: line!() as usize,
                col: column!() as usize,
                message: format!("Unexpected token kind '{token:?}'. Expected \
                '{expected_token_kind:?}'"),
            });
        }
        Ok(token)
    }
}
