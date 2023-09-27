use std::cell::RefCell;
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::{Lexer, Token, TokenKind};

impl Lexer {
    #[must_use]
    pub fn new(input: &str, error_diag: Arc<RefCell<ErrorDiagnosis>>) -> Self {
        let chars = input.chars().collect();
        Self {
            chars,
            position: 0,
            row: 1,
            col: 1,
            error_diag,
        }
    }

    pub fn lex(&mut self) -> Vec<Token> {
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

    fn new_token_with_value(&self, kind: TokenKind, value: String) -> Token {
        Token {
            kind,
            position: (self.row, self.col),
            value: Some(value),
        }
    }

    fn new_token(&self, kind: TokenKind) -> Token {
        Token {
            kind,
            position: (self.row, self.col),
            value: None,
        }
    }

    fn parse_token(&mut self) -> Token {
        let token = match self.peek() {
            '\0' => self.new_token(TokenKind::Eof),
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

        if matches!(token.kind, TokenKind::Whitespace) || matches!(token.kind, TokenKind::Comment) {
            return self.parse_token();
        }
        token
    }

    fn peek(&self) -> char {
        self.peek_ahead(0)
    }

    fn peek_ahead(&self, ahead: usize) -> char {
        if self.position + ahead >= self.chars.len() {
            return char::default();
        }

        self.chars[self.position + ahead]
    }

    fn consume(&mut self) {
        self.col += 1;
        self.position += 1;
    }

    fn handle_p(&mut self) -> Token {
        // Consume opening quote.
        self.consume();
        let mut c = self.peek();
        self.consume();
        if c == '\\' {
            c = self.peek();
            self.consume();
        }

        // Consume closing quote.
        self.consume();
        self.new_token_with_value(TokenKind::PKeyword, String::from(c))
    }

    fn handle_unknown(&mut self) -> Token {
        let c = self.peek();
        self.consume();

        self.new_token_with_value(TokenKind::Unknown, String::from(c))
    }

    fn handle_comment(&mut self) -> Token {
        // Consume the comment tag
        self.consume();

        let mut c = self.peek();
        while c != '\n' {
            self.consume();
            c = self.peek();
        }

        self.new_token(TokenKind::Comment)
    }

    fn handle_operator(&mut self) -> Token {
        let mut buf = String::with_capacity(2);
        let operator = self.peek();
        buf.push(operator);
        self.consume();

        match operator {
            '-' => {
                if self.peek() == '=' {
                    buf.push(self.peek());
                    self.consume();
                } else if self.peek() == '>' {
                    buf.push(self.peek());
                    self.consume();
                }
            }
            '>' | '<' | '!' | '=' | '+' | '*' | '/' | '%' => {
                if self.peek() == '=' {
                    buf.push(self.peek());
                    self.consume();
                }
            }
            _ => {}
        }

        let kind: TokenKind = match buf.as_str() {
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
            _ => panic!("Unknown operator: {buf}"),
        };

        self.new_token(kind)
    }

    fn handle_punctuation(&mut self) -> Token {
        let c = self.peek();

        let kind = match c {
            '(' => TokenKind::OpenParen,
            ')' => TokenKind::CloseParen,
            '{' => TokenKind::OpenBrace,
            '}' => TokenKind::CloseBrace,
            '[' => TokenKind::OpenBracket,
            ']' => TokenKind::CloseBracket,
            ',' => TokenKind::Comma,
            ':' => TokenKind::Colon,
            ';' => TokenKind::Semicolon,
            _ => unreachable!("Unknown punctuation: {c}"),
        };
        self.consume();

        self.new_token(kind)
    }

    fn handle_whitespace(&mut self) -> Token {
        let mut c = self.peek();
        while c.is_whitespace() {
            self.consume();
            if c == '\n' {
                self.row += 1;
                self.col = 1;
            }
            c = self.peek();
        }

        self.new_token(TokenKind::Whitespace)
    }

    fn handle_yarn(&mut self) -> Token {
        let mut buf = String::with_capacity(256);
        // Consume the opening quote.
        self.consume();

        let mut c = self.peek();
        while c != char::default() && c != '"' && c != '\n' {
            buf.push(c);
            self.consume();
            c = self.peek();

            if c == '\\' {
                buf.push(c);
                self.consume();
                c = self.peek();
            }
        }

        if c == '"' {
            // Consume the closing quote.
            self.consume();
        }

        let token = self.new_token_with_value(TokenKind::Yarn, buf);
        if c != '"' {
            self.error_diag
                .borrow_mut()
                .expected_different_token_error(&token, TokenKind::DoubleQuote);
        }

        token
    }

    fn handle_number(&mut self) -> Token {
        let mut buf = String::with_capacity(256);

        let mut c = self.peek();
        while c.is_ascii_digit() {
            buf.push(c);
            self.consume();
            c = self.peek();
        }

        self.new_token_with_value(TokenKind::Number, buf)
    }

    fn handle_identifier(&mut self) -> Token {
        let mut buf = String::with_capacity(256);

        let mut c = self.peek();
        while c.is_alphabetic() || c == '_' && !c.is_whitespace() {
            buf.push(c);
            self.consume();
            c = self.peek();
        }

        let kind = match buf.as_str() {
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

        if kind == TokenKind::Identifier {
            self.new_token_with_value(kind, buf)
        } else {
            self.new_token(kind)
        }
    }
}
