use std::collections::HashMap;
use crate::ast::Ast;
use crate::lexer::{Keyword, Lexer, SyntaxError, Token, TokenKind};

pub struct Parser {
    lexer: Lexer,
    row: usize,
    col: usize,
}

#[derive(Debug)]
pub struct Expression {
    value: String,
}

#[derive(Debug)]
pub struct Identifier {
    value: String,
}

#[derive(Debug)]
pub struct Function {
    name: String,
    parameters: HashMap<String, Identifier>,
    body: Vec<Expression>,
}

impl Parser {
    pub const fn new(lexer: Lexer) -> Self {
        Self { lexer, row: 0, col: 0 }
    }

    pub fn parse(&mut self) -> Result<Ast, SyntaxError> {
        self.lexer.reset();
        self.lexer.lex()?;

        let func = self.parse_function()?;
        dbg!(func);

        Ok(Ast)
    }

    fn parse_function(&mut self) -> Result<Function, SyntaxError> {
        self.expect_keyword(Keyword::Func)?;
        self.lexer.consume_token();

        let function_name_token = self.expect_token_kind(&TokenKind::Identifier)?;
        let function_name = String::from(function_name_token.value.as_ref().unwrap());
        self.lexer.consume_token();

        self.expect_token(&Token {
            kind: TokenKind::Punctuation,
            value: Some(String::from("(")),
        })?;
        self.lexer.consume_token();

        // TODO: Parse parameters

        self.expect_token(&Token {
            kind: TokenKind::Punctuation,
            value: Some(String::from(")")),
        })?;
        self.lexer.consume_token();

        self.expect_token(&Token {
            kind: TokenKind::Punctuation,
            value: Some(String::from(":")),
        })?;
        self.lexer.consume_token();

        self.expect_token_kind(&TokenKind::Identifier)
            .or(self.expect_token_kind
            (&TokenKind::DataType))?;

        self.lexer.consume_token();

        self.expect_token(&Token {
            kind: TokenKind::Punctuation,
            value: Some(String::from("{")),
        })?;
        self.lexer.consume_token();

        // TODO: Parse body
        self.expect_token(&Token {
            kind: TokenKind::Punctuation,
            value: Some(String::from("}")),
        })?;
        self.lexer.consume_token();

        Ok(Function {
            name: function_name,
            parameters: HashMap::new(),
            body: Vec::new(),
        })
    }

    fn expect_token_kind(&self, expected_token_kind: &TokenKind) -> Result<&Token, SyntaxError> {
        let token = self.lexer.token().unwrap();
        let token_kind = &token.kind;
        if token_kind != expected_token_kind {
            return Err(SyntaxError {
                row: 0,
                col: 0,
                message: format!("Unexpected token kind '{token:?}'. Expected \
                '{expected_token_kind:?}'"),
            });
        }

        Ok(token)
    }

    fn expect_token(&self, expected_token: &Token) -> Result<&Token, SyntaxError> {
        let token = self.expect_token_kind(&expected_token.kind)?;
        let token_kind = &token.kind;
        let expected_token_kind = &expected_token.kind;
        if *token_kind != *expected_token_kind {
            return Err(SyntaxError {
                row: 0,
                col: 0,
                message: format!("Unexpected token kind '{token:?}'. Expected \
                '{expected_token:?}'"),
            });
        }

        if token.value != expected_token.value {
            return Err(SyntaxError {
                row: 0,
                col: 0,
                message: format!("Unexpected token '{token:?}'. Expected \
                '{expected_token:?}'"),
            });
        }

        if token.value.is_some() {
            let token_value = token.value.as_ref().unwrap();
            let expected_token_value = expected_token.value.as_ref().unwrap();
            if token_value != expected_token_value {
                return Err(SyntaxError {
                    row: 0,
                    col: 0,
                    message: format!("Unexpected token '{token_kind:?}'. Expected \
                    '{expected_token_kind:?}'"),
                });
            }
        }

        Ok(token)
    }

    fn expect_keyword(&self, keyword: Keyword) -> Result<&Token, SyntaxError> {
        let token = self.lexer.token().unwrap();
        if token.kind == TokenKind::Keyword {
            match Keyword::try_from(token.value.as_ref().expect("No value found").as_str()) {
                Ok(kw) => {
                    if kw == keyword {
                        return Ok(token);
                    }
                }
                Err(err) => return Err(SyntaxError {
                    row: 0,
                    col: 0,
                    message: err.keyword,
                }),
            };
        }


        Err(SyntaxError {
            row: 0,
            col: 0,
            message: String::from(format!("Unexpected keyword {token:?}. Expected {keyword:?}")),
        })
    }
}
