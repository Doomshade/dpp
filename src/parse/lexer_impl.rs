//! The tokenizer for the dpp language.

use crate::parse::error_diagnosis::{ErrorDiagnosis, SyntaxError};
use std::cell::RefCell;
use std::rc::Rc;

use crate::parse::lexer::{Token, TokenKind};
use crate::parse::Lexer;

impl<'a, 'b> Lexer<'a, 'b> {
    ///
    /// Lexes the input into a vector of Tokens.
    ///
    /// # Arguments
    ///
    ///
    /// returns: Vector of Tokens.
    ///
    /// # Examples
    ///
    /// ```
    /// let input: &str = "let x = 5;";
    /// let error_diag = Arc::new(RefCell::new(ErrorDiagnosis::new("test.dpp", input)));
    /// let mut lexer = Lexer::new(input, error_diag.clone());
    /// let tokens = lexer.lex();
    /// // ...
    /// // The tokens then can be used for parsing.
    /// ```
    pub fn lex(&mut self) -> Result<Vec<Token<'a>>, SyntaxError> {
        let mut tokens = Vec::new();
        let mut token = self.lex_token();
        loop {
            let is_eof = token.kind() == TokenKind::Eof;
            tokens.push(token);
            if is_eof {
                break;
            }
            token = self.lex_token();
        }
        self.error_diag.borrow().check_errors()?;
        Ok(tokens)
    }

    fn lex_token(&mut self) -> Token<'a> {
        // Parse the token based on the first character prefix.
        let token = match self.peek() {
            '\0' => self.new_token(TokenKind::Eof, "EOF"),
            'a'..='z' | 'A'..='Z' | '_' => self.identifier(),
            '0'..='9' => self.number(),
            '"' => self.yarn(),
            ' ' | '\t' | '\n' | '\r' => self.whitespace(),
            ';' | '(' | ')' | '{' | '}' | ',' | '[' | ']' | ':' => self.punctuation(),
            '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '~' => {
                self.operator()
            }
            '#' => self.comment(),
            '\'' => self.p(),
            _ => self.unknown(),
        };

        // If it's a whitespace or a comment, try to parse the next token as this one is useless
        // to the parser. The Comment token could be useful for error handling later on,
        // but we don't need it for now.
        if matches!(token.kind(), TokenKind::Whitespace)
            || matches!(token.kind(), TokenKind::Comment)
        {
            return self.lex_token();
        }
        token
    }

    fn p(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;

        end += self.advance(); // Consume opening quote.
        if self.peek() == '\\' {
            // TODO: Handle escaped characters.
            end += self.advance(); // Consume the escaped character.
        }
        end += self.advance(); // Consume the character.

        if self.peek() != '\'' {
            self.error_diag
                .borrow_mut()
                .expected_different_token_error(&self.new_token(TokenKind::P, ""), TokenKind::P);
            return self.new_token(TokenKind::Eof, "EOF");
        }

        end += self.advance(); // Consume closing quote.
        self.new_token(TokenKind::P, &self.raw_input[start + 1..end - 1])
    }

    fn unknown(&mut self) -> Token<'a> {
        let end = self.advance();

        self.new_token(TokenKind::Unknown, &self.raw_input[self.cursor - 1..end])
    }

    fn comment(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;

        end += self.advance(); // Consume the '#' comment tag.

        while self.peek() != '\n' {
            end += self.advance();
        }

        self.new_token(TokenKind::Comment, &self.raw_input[start..end])
    }

    fn operator(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;

        match self.peek() {
            '-' => {
                end += self.advance();
                if self.peek() == '=' || self.peek() == '>' {
                    end += self.advance();
                }
            }
            '>' | '<' | '!' | '=' | '+' | '*' | '/' | '%' => {
                end += self.advance();
                if self.peek() == '=' {
                    end += self.advance();
                }
            }
            _ => {
                end += self.advance();
            }
        }

        let op = &self.raw_input[start..end];
        let kind: TokenKind = match op {
            "->" => TokenKind::Arrow,
            ">" => TokenKind::Greater,
            ">=" => TokenKind::GreaterEqual,
            "<" => TokenKind::Less,
            "<=" => TokenKind::LessEqual,
            "!" => TokenKind::Bang,
            "=" => TokenKind::Equal,
            "!=" => TokenKind::BangEqual,
            "==" => TokenKind::EqualEqual,
            "*" => TokenKind::Star,
            "/" => TokenKind::ForwardSlash,
            "\\" => TokenKind::BackSlash,
            "+" => TokenKind::Plus,
            "-" => TokenKind::Dash,
            "+-" => TokenKind::PlusDash,
            "+=" => TokenKind::PlusEqual,
            "-=" => TokenKind::MinusEqual,
            _ => panic!("Unknown operator: {op}"),
        };

        self.new_token(kind, op)
    }

    fn punctuation(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;
        let kind = match self.peek() {
            '(' => TokenKind::OpenParen,
            ')' => TokenKind::CloseParen,
            '{' => TokenKind::OpenBrace,
            '}' => TokenKind::CloseBrace,
            '[' => TokenKind::OpenBracket,
            ']' => TokenKind::CloseBracket,
            ',' => TokenKind::Comma,
            ':' => TokenKind::Colon,
            ';' => TokenKind::Semicolon,
            _ => unreachable!("Unknown punctuation: {}", self.peek()),
        };
        end += self.advance();

        self.new_token(kind, &self.raw_input[start..end])
    }

    fn whitespace(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut _end = start;
        while self.peek().is_whitespace() {
            if self.peek() == '\n' {
                self.row += 1;
                self.col = 0;
            }
            _end += self.advance();
        }

        self.new_token(TokenKind::Whitespace, "")
    }

    fn yarn(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;
        end += self.advance(); // Consume the opening quote.

        while self.peek() != char::default() && self.peek() != '"' && self.peek() != '\n' {
            end += self.advance(); // Add the character.

            if self.peek() == '\\' {
                end += self.advance();
                let _x = match self.peek() {
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    '\\' => '\\',
                    '0' => '\0',
                    _ => {
                        self.error_diag.borrow_mut().invalid_escaped_character(
                            self.row,
                            self.col,
                            self.peek(),
                        );
                        self.peek()
                    }
                };
                end += self.advance();
            }
        }

        if self.peek() == '"' {
            let _ = self.advance(); // Consume the closing quote.
        } else {
            self.error_diag.borrow_mut().expected_different_token_error(
                &self.new_token(TokenKind::Yarn, &self.raw_input[start + 1..end]),
                TokenKind::DoubleQuote,
            );
        }
        self.new_token(TokenKind::Yarn, &self.raw_input[start + 1..end - 1])
    }

    fn number(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;

        while self.peek().is_ascii_digit() {
            end += self.advance();
        }

        if self.peek() == '.' {
            if !self.peek().is_ascii_digit() {
                self.error_diag
                    .borrow_mut()
                    .invalid_number(self.row, self.col);
            }
            while self.peek().is_ascii_digit() {
                end += self.advance();
            }
        }

        self.new_token(TokenKind::Number, &self.raw_input[start..end])
    }

    fn identifier(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;
        end += self.advance();

        while self.peek().is_ascii_digit()
            || self.peek().is_alphabetic()
            || self.peek() == '_' && !self.peek().is_whitespace()
        {
            end += self.advance();
        }

        let ident_value = &self.raw_input[start..end];
        let kind = match ident_value {
            "xxlpp" => TokenKind::XxlppKeyword,
            "pp" => TokenKind::PpKeyword,
            "spp" => TokenKind::SppKeyword,
            "xspp" => TokenKind::XsppKeyword,
            "p" => TokenKind::PKeyword,
            "nopp" => TokenKind::NoppKeyword,
            "booba" => TokenKind::BoobaKeyword,
            "if" => TokenKind::IfKeyword,
            "while" => TokenKind::WhileKeyword,
            "else" => TokenKind::ElseKeyword,
            "for" => TokenKind::ForKeyword,
            "to" => TokenKind::ToKeyword,
            "let" => TokenKind::LetKeyword,
            "bye" => TokenKind::ByeKeyword,
            "pprint" => TokenKind::PprintKeyword,
            "pprintln" => TokenKind::PprintlnKeyword,
            "ppanic" => TokenKind::PpanicKeyword,
            "ppin" => TokenKind::PpinKeyword,
            "FUNc" => TokenKind::FUNcKeyword,
            "do" => TokenKind::DoKeyword,
            "loop" => TokenKind::LoopKeyword,
            "yem" => TokenKind::YemKeyword,
            "nom" => TokenKind::NomKeyword,
            "break" => TokenKind::BreakKeyword,
            "continue" => TokenKind::ContinueKeyword,
            "switch" => TokenKind::SwitchKeyword,
            "case" => TokenKind::CaseKeyword,
            "yarn" => TokenKind::YarnKeyword,
            _ => TokenKind::Identifier,
        };

        self.new_token(kind, ident_value)
    }
}
