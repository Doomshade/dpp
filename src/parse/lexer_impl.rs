//! The tokenizer for the dpp language.

use crate::parse::error_diagnosis::ErrorDiagnosis;
use std::cell::RefCell;
use std::rc::Rc;

use crate::parse::lexer::{Token, TokenKind};
use crate::parse::Lexer;

impl<'a, 'b> Lexer<'a, 'b> {
    /// # Arguments
    ///
    /// * `input`: The translation unit input.
    /// * `error_diag`: The error diagnostics.
    ///
    /// returns: Lexer
    #[must_use]
    pub fn new(input: &'a str, error_diag: Rc<RefCell<ErrorDiagnosis<'a, 'b>>>) -> Self {
        // Create a vector of characters from the input string. This is so that we can access the
        // characters by index. Unfortunately this will take up more memory, but as soon as the
        // lexer goes out of scope, the vector will be dropped.

        // NOTE: We would normally use an iterator here, but the problem is that we need to
        // be able to peek inside the iterator. The Peekable trait allows it, HOWEVER: the trait
        // consumes the iterator, which means that we can't use it anymore. So we have to use a
        // vector instead.
        let chars = input.chars().collect();
        Self {
            raw_input: input,
            chars,
            cursor: 0,
            row: 1,
            col: 1,
            error_diag,
        }
    }
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
    pub fn lex(&mut self) -> Vec<Token<'a>> {
        let mut tokens = Vec::new();
        let mut token = self.parse_token();
        loop {
            let is_eof = token.kind() == TokenKind::Eof;
            tokens.push(token);
            if is_eof {
                break;
            }
            token = self.parse_token();
        }
        tokens
    }

    fn new_token(&self, kind: TokenKind, value: &'a str) -> Token<'a> {
        Token::new(kind, (self.row, self.col - 1), value)
    }

    fn parse_token(&mut self) -> Token<'a> {
        // Parse the token based on the first character prefix.
        let token = match self.peek() {
            '\0' => self.new_token(TokenKind::Eof, "EOF"),
            'a'..='z' | 'A'..='Z' | '_' => self.handle_identifier(),
            '0'..='9' => self.handle_number(),
            '"' => self.handle_yarn(),
            ' ' | '\t' | '\n' | '\r' => self.handle_whitespace(),
            ';' | '(' | ')' | '{' | '}' | ',' | '[' | ']' | ':' => self.handle_punctuation(),
            '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '~' => {
                self.handle_operator()
            }
            '#' => self.handle_comment(),
            '\'' => self.handle_p(),
            _ => self.handle_unknown(),
        };

        // If it's a whitespace or a comment, try to parse the next token as this one is useless
        // to the parser. The Comment token could be useful for error handling later on,
        // but we don't need it for now.
        if matches!(token.kind(), TokenKind::Whitespace)
            || matches!(token.kind(), TokenKind::Comment)
        {
            return self.parse_token();
        }
        token
    }

    fn peek(&self) -> char {
        self.peek_ahead(0)
    }

    fn peek_ahead(&self, ahead: usize) -> char {
        if self.cursor + ahead >= self.chars.len() {
            return char::default();
        }

        self.chars[self.cursor + ahead]
    }

    #[must_use]
    fn advance(&mut self) -> usize {
        let advanced_bytes = self.peek().len_utf8();
        if advanced_bytes > 1 {
            println!("YO");
        }
        self.col += 1;
        self.cursor += 1;
        advanced_bytes
    }

    fn handle_p(&mut self) -> Token<'a> {
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

    fn handle_unknown(&mut self) -> Token<'a> {
        let end = self.advance();

        self.new_token(TokenKind::Unknown, &self.raw_input[self.cursor - 1..end])
    }

    fn handle_comment(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;

        end += self.advance(); // Consume the '#' comment tag.

        while self.peek() != '\n' {
            end += self.advance();
        }

        self.new_token(TokenKind::Comment, &self.raw_input[start..end])
    }

    fn handle_operator(&mut self) -> Token<'a> {
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

    fn handle_punctuation(&mut self) -> Token<'a> {
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

    fn handle_whitespace(&mut self) -> Token<'a> {
        let start = self.cursor;
        let mut end = start;
        while self.peek().is_whitespace() {
            if self.peek() == '\n' {
                self.row += 1;
                self.col = 1;
            }
            end += self.advance();
        }

        self.new_token(TokenKind::Whitespace, "")
    }

    fn handle_yarn(&mut self) -> Token<'a> {
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

        let token = self.new_token(TokenKind::Yarn, &self.raw_input[start + 1..end]);
        if self.peek() == '"' {
            let _ = self.advance(); // Consume the closing quote.
        } else {
            self.error_diag
                .borrow_mut()
                .expected_different_token_error(&token, TokenKind::DoubleQuote);
        }

        token
    }

    fn handle_number(&mut self) -> Token<'a> {
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

    fn handle_identifier(&mut self) -> Token<'a> {
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
