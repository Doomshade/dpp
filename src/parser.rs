use crate::ast::Ast;
use crate::lexer::{Keyword, Lexer, SyntaxError, Token, TokenKind};

pub struct Parser {
    lexer: Lexer,
}

pub struct Function;

impl Parser {
    pub fn new(lexer: Lexer) -> Self {
        Self { lexer }
    }

    pub fn parse(&mut self) -> Result<Ast, SyntaxError> {
        self.lexer.reset();
        let token = self.expect_token(TokenKind::Eof)?;
        println!("Found token: {token:?}");

        Ok(Ast)
    }

    fn parse_function(&mut self) -> Result<Function, SyntaxError> {
        match self.expect_keyword(Keyword::Func) {
            Ok(token) => println!("{token:?}"),
            Err(err) => panic!("{}", err),
        }

        Ok(Function)
    }

    fn expect_token(&mut self, expected_token_kind: TokenKind) -> Result<Token, SyntaxError> {
        let token = self.lexer.next_token()?;
        if token.kind == expected_token_kind {
            println!("OK");
            return Ok(token);
        }
        Err(SyntaxError::new(
            0,
            0,
            format!("Unexpected token '{token:?}'. Expected '{expected_token_kind:?}'"),
        ))
    }

    fn expect_keyword(&mut self, keyword: Keyword) -> Result<Token, SyntaxError> {
        let token = self.lexer.next_token()?;
        if token.kind == TokenKind::Keyword {
            match Keyword::try_from(token.value.as_ref().expect("No value found").as_str()) {
                Ok(kw) => {
                    if kw == keyword {
                        return Ok(token);
                    }
                }
                Err(err) => return Err(SyntaxError::new(0, 0, err.keyword)),
            };
        }

        Err(SyntaxError::new(0, 0, String::from("nothin")))
    }
}
