use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

use crate::error_diagnosis::ErrorDiagnosis;

#[derive(Debug)]
pub struct SyntaxError {
    pub file: String,
    pub row: usize,
    pub col: usize,
    pub message: String,
}

#[derive(Debug)]
pub struct UnknownKeywordError {
    pub keyword: String,
}

#[derive(Debug)]
pub struct UnknownDataTypeError {
    pub keyword: String,
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Syntax error in file {} at {}:{} - {}",
            self.file, self.row, self.col, self.message
        )
    }
}

impl Display for UnknownKeywordError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unknown keyword: {}", self.keyword)
    }
}

impl Display for UnknownDataTypeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unknown data type: {}", self.keyword)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Keyword {
    Let,
    Bye,
    Pprint,
    Ppanic,
    Ppin,
    Func,
}

#[derive(Debug, PartialEq, Eq)]
pub enum DataType {
    // u64
    Xxlpp,
    // u32
    Pp,
    // u16
    Spp,
    // u8
    Xspp,
    // void
    Nopp,
    // String
    Thread,
    // bool
    Boob,
    // char
    P,
}

#[derive(Debug)]
pub struct Token {
    kind: TokenKind,
    /// Row, Column
    position: (u32, u32),
    value: Option<String>,
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(value) = &self.value {
            write!(f, "{} ({})", value, self.kind)
        } else {
            write!(f, "\"{}\"", self.kind)
        }
    }
}

impl Token {
    #[must_use]
    pub fn value(&self) -> Option<String> {
        if let Some(val) = &self.value {
            return Some(String::from(val));
        }
        None
    }

    #[must_use]
    pub const fn row(&self) -> u32 {
        self.position.0
    }
    #[must_use]
    pub const fn col(&self) -> u32 {
        self.position.1
    }

    #[must_use]
    pub const fn position(&self) -> (u32, u32) {
        self.position
    }

    #[must_use]
    pub const fn kind(&self) -> TokenKind {
        self.kind
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenKind {
    Identifier,
    Number,
    BangEqual,
    Comment,
    Whitespace,
    Eof,
    Unknown,
    EqualEqual,
    Equal,
    Bang,
    Star,
    ForwardSlash,
    BackSlash,
    Plus,
    MinusEqual,
    PlusEqual,
    PlusDash,
    Dash,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    NomKeyword,
    YemKeyword,
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,
    Colon,
    Semicolon,
    Ampersand,
    Pipe,
    Comma,
    IfKeyword,  // if
    LetKeyword, // let
    ByeKeyword, // return
    FUNcKeyword,
    // func
    PprintKeyword, // print()
    PpanicKeyword, // panic()
    PpinKeyword,   // read()
    XxlppType,     // u64
    PpType,        // u32
    SppType,       // u16
    XsppType,      // u8
    PType,         // char
    BoobaType,     // bool
    FiberType,     // String
    NoppType,
    // void
    ForKeyword,
    ElseKeyword,
    DoubleQuote,
    ToKeyword,
    Arrow,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let text_representation = match self {
            Self::Identifier => "identifier",
            Self::Number => "number",
            Self::FiberType => "fiber",
            Self::BangEqual => "!=",
            Self::Comment => "",
            Self::Whitespace => "",
            Self::Eof => "",
            Self::Unknown => "",
            Self::EqualEqual => "==",
            Self::Equal => "=",
            Self::Bang => "!",
            Self::Star => "*",
            Self::ForwardSlash => "/",
            Self::BackSlash => "\\",
            Self::Plus => "+",
            Self::MinusEqual => "-=",
            Self::PlusEqual => "+=",
            Self::PlusDash => "+-",
            Self::Dash => "-",
            Self::Greater => ">",
            Self::GreaterEqual => ">=",
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::NomKeyword => "nom",
            Self::YemKeyword => "yem",
            Self::OpenParen => "(",
            Self::CloseParen => ")",
            Self::OpenBrace => "{",
            Self::CloseBrace => "}",
            Self::OpenBracket => "[",
            Self::CloseBracket => "]",
            Self::Colon => ":",
            Self::Semicolon => ";",
            Self::Ampersand => "&",
            Self::Pipe => "|",
            Self::Comma => ",",
            Self::IfKeyword => "if",
            Self::LetKeyword => "let",
            Self::ByeKeyword => "bye",
            Self::PprintKeyword => "pprint",
            Self::PpanicKeyword => "ppanic",
            Self::PpinKeyword => "ppin",
            Self::FUNcKeyword => "FUNc",
            Self::ElseKeyword => "else",
            Self::ForKeyword => "for",
            Self::XxlppType => "data type \"xxlpp\"",
            Self::PpType => "data type \"pp\"",
            Self::SppType => "data type \"spp\"",
            Self::XsppType => "data type \"xspp\"",
            Self::PType => "data type \"p\"",
            Self::BoobaType => "data type \"booba\"",
            Self::NoppType => "void data type \"nopp\"",
            Self::DoubleQuote => "\"\"\"",
            Self::ToKeyword => "to",
            Self::Arrow => "->",
        };
        write!(f, "{text_representation}")
    }
}

#[derive(Debug)]
pub struct Lexer {
    chars: Vec<char>,
    position: usize,
    row: u32,
    col: u32,
    error_diag: Rc<RefCell<ErrorDiagnosis>>,
}

impl Lexer {
    #[must_use]
    pub fn new(input: &str, error_diag: Rc<RefCell<ErrorDiagnosis>>) -> Self {
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
        while token.kind() != TokenKind::Eof {
            tokens.push(token);
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
            '"' => self.handle_fiber(),
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
        self.new_token_with_value(TokenKind::PType, String::from(c))
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

    fn handle_fiber(&mut self) -> Token {
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

        let token = self.new_token_with_value(TokenKind::FiberType, buf);
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
            "xxlpp" => TokenKind::XxlppType,
            "pp" => TokenKind::PpType,
            "spp" => TokenKind::SppType,
            "xspp" => TokenKind::XsppType,
            "p" => TokenKind::PType,
            "nopp" => TokenKind::NoppType,
            "booba" => TokenKind::BoobaType,
            "if" => TokenKind::IfKeyword,
            "else" => TokenKind::ElseKeyword,
            "fori" => TokenKind::ForKeyword,
            "to" => TokenKind::ToKeyword,
            "let" => TokenKind::LetKeyword,
            "bye" => TokenKind::ByeKeyword,
            "pprint" => TokenKind::PprintKeyword,
            "ppanic" => TokenKind::PpanicKeyword,
            "ppin" => TokenKind::PpinKeyword,
            "FUNc" => TokenKind::FUNcKeyword,
            "yem" => TokenKind::YemKeyword,
            "nom" => TokenKind::NomKeyword,
            _ => TokenKind::Identifier,
        };

        if kind == TokenKind::Identifier {
            self.new_token_with_value(kind, buf)
        } else {
            self.new_token(kind)
        }
    }
}
