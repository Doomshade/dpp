use std::fmt;
use crate::lexer::{Lexer, SyntaxError, Token, TokenKind};

pub struct Parser {
    lexer: Lexer,
}

pub struct Program {
    expression: Option<Box<Expression>>,
}

impl Program {
    pub fn expression(&self) -> &Option<Box<Expression>> {
        &self.expression
    }
}

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

pub struct BinaryExpression {
    lhs: Box<Expression>,
    op: Op,
    rhs: Box<Expression>,
}

impl BinaryExpression {
    pub fn lhs(&self) -> &Expression {
        &self.lhs
    }

    pub fn op(&self) -> &Op {
        &self.op
    }

    pub fn rhs(&self) -> &Expression {
        &self.rhs
    }
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

#[derive(Copy, Clone, Debug)]
pub enum Op {
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl Parser {
    pub const fn new(lexer: Lexer) -> Self {
        Self { lexer }
    }

    pub fn parse(&mut self) -> Result<Program, SyntaxError> {
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
            "-" => Ok(Op::Subtract),
            "*" => Ok(Op::Multiply),
            "/" => Ok(Op::Divide),
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
