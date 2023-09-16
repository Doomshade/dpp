use crate::ast::Ast;
use crate::lexer::{Keyword, Lexer, SyntaxError, Token, TokenKind};

pub struct Parser {
    lexer: Lexer,
    row: usize,
    col: usize,
}

#[derive(Debug)]
pub struct Program {
    binary_expression: BinaryExpression,
}

#[derive(Debug)]
pub struct BinaryExpression {
    num1: i64,
    op: Op,
    num2: i64,
}

#[derive(Debug)]
pub enum Op {
    Add,
}

impl Parser {
    pub const fn new(lexer: Lexer) -> Self {
        Self { lexer, row: 0, col: 0 }
    }

    pub fn parse(&mut self) -> Result<Program, SyntaxError> {
        self.lexer.reset();
        self.lexer.lex()?;
        self.parse_program()
    }

    fn parse_program(&mut self) -> Result<Program, SyntaxError> {
        let binary_expression = self.parse_binary_expression()?;
        Ok(Program { binary_expression })
    }

    fn parse_binary_expression(&mut self) -> Result<BinaryExpression, SyntaxError> {
        let num1 = self.expect_number()?;
        self.lexer.consume_token();
        let op = self.expect_operator()?;
        self.lexer.consume_token();
        let num2 = self.expect_number()?;
        self.lexer.consume_token();
        Ok(BinaryExpression { num1, op, num2 })
    }

    fn expect_number(&self) -> Result<i64, SyntaxError> {
        let num_token = self.expect_token_kind(TokenKind::Number)?;
        num_token.value.as_ref().expect("Expected value").parse::<i64>().map_err(|_| SyntaxError {
            row: 0,
            col: 0,
            message: "".to_string(),
        })
    }

    fn expect_operator(&self) -> Result<Op, SyntaxError> {
        let op_token = self.expect_token_kind(TokenKind::Operator)?;
        return match op_token.value.as_ref().expect("Expected value").as_str() {
            "+" => Ok(Op::Add),
            _ => Err(SyntaxError {
                row: 0,
                col: 0,
                message: "".to_string(),
            })
        };
    }

    fn expect_token_kind(&self, expected_token_kind: TokenKind) -> Result<&Token, SyntaxError> {
        let token = self.lexer.token().expect("No token found");
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
