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
    row: u32,
    col: u32,
    value: Option<String>,
}

impl Token {
    #[must_use]
    pub fn value(&self) -> Option<String> {
        if let Some(val) = &self.value {
            return Some(String::from(val));
        }
        None
    }

    pub fn row(&self) -> u32 {
        self.row
    }
    pub fn col(&self) -> u32 {
        self.col
    }

    pub fn kind(&self) -> TokenKind {
        self.kind
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenKind {
    Identifier,
    Number,
    Fiber,
    Character,
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
    IfKeyword,     // if
    LetKeyword,    // let
    ByeKeyword,    // return
    PprintKeyword, // print()
    PpanicKeyword, // panic()
    PpinKeyword,   // read()
    XxlppType,     // u64
    PpType,        // u32
    FUNcKeyword,   // func
    SppType,       // u16
    XsppType,      // u8
    NoppType,      // void
    PType,         // char
    BoobaType,     // bool
    ThreadType,    // String
    ElseKeyword,
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
            row: 0,
            col: 0,
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

    fn parse_token(&mut self) -> Token {
        let token = match self.peek() {
            '\0' => Token {
                kind: TokenKind::Eof,
                row: self.row,
                col: self.col,
                value: None,
            },
            'a'..='z' | 'A'..='Z' | '_' => self.handle_identifier(),
            '0'..='9' => self.handle_number(),
            '"' => self.handle_string(),
            ' ' | '\t' | '\n' | '\r' => self.handle_whitespace(),
            ';' | '(' | ')' | '{' | '}' | ',' | '[' | ']' | ':' => self.handle_punctuation(),
            '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '~' => {
                self.handle_operator()
            }
            '#' => self.handle_comment(),
            '\'' => self.handle_char(),
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

    fn handle_char(&mut self) -> Token {
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
        Token {
            kind: TokenKind::Character,
            row: self.row,
            col: self.col,
            value: Some(String::from(c)),
        }
    }

    fn handle_unknown(&mut self) -> Token {
        let c = self.peek();
        self.consume();

        Token {
            kind: TokenKind::Unknown,
            row: self.row,
            col: self.col,
            value: Some(String::from(c)),
        }
    }

    fn handle_comment(&mut self) -> Token {
        // Consume the comment tag
        self.consume();

        let mut c = self.peek();
        while c != '\n' {
            self.consume();
            c = self.peek();
        }

        Token {
            kind: TokenKind::Comment,
            row: self.row,
            col: self.col,
            value: None,
        }
    }

    fn handle_operator(&mut self) -> Token {
        let mut buf = String::with_capacity(2);
        buf.push(self.peek());
        self.consume();

        match self.peek() {
            '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '~' => {
                buf.push(self.peek());
                self.consume();
            }
            _ => {}
        }

        let kind: TokenKind = match buf.as_str() {
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

        Token {
            kind,
            row: self.row,
            col: self.col,
            value: Some(buf),
        }
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

        Token {
            kind,
            row: self.row,
            col: self.col,
            value: Some(String::from(c)),
        }
    }

    fn handle_whitespace(&mut self) -> Token {
        let mut c = self.peek();
        while c.is_whitespace() {
            self.consume();
            if c == '\n' {
                self.row += 1;
                self.col = 0;
            }
            c = self.peek();
        }

        Token {
            kind: TokenKind::Whitespace,
            row: self.row,
            col: self.col,
            value: None,
        }
    }

    fn handle_string(&mut self) -> Token {
        let mut buf = String::with_capacity(256);
        // Consume the opening quote.
        self.consume();

        let mut c = self.peek();
        while c != char::default() && c != '"' {
            buf.push(c);
            self.consume();
            c = self.peek();

            if c == '\\' {
                buf.push(c);
                self.consume();
                c = self.peek();
            }
        }

        if c == char::default() {
            self.error_diag.borrow_mut().handle("Unterminated string.");
            return Token {
                kind: TokenKind::Fiber,
                row: self.row,
                col: self.col,
                value: Some(buf),
            };
        }
        // Consume the closing quote.
        self.consume();

        Token {
            kind: TokenKind::Fiber,
            row: self.row,
            col: self.col,
            value: Some(buf),
        }
    }

    fn handle_number(&mut self) -> Token {
        let mut buf = String::with_capacity(256);

        let mut c = self.peek();
        while c.is_ascii_digit() {
            buf.push(c);
            self.consume();
            c = self.peek();
        }

        Token {
            kind: TokenKind::Number,
            row: self.row,
            col: self.col,
            value: Some(buf),
        }
    }

    fn handle_identifier(&mut self) -> Token {
        let mut buf = String::with_capacity(256);

        let mut c = self.peek();
        while c.is_alphabetic() || c == '_' && !c.is_whitespace() {
            buf.push(c);
            self.consume();
            c = self.peek();
        }
        let token_kind = match buf.as_str() {
            "xxlpp" => TokenKind::XxlppType,
            "pp" => TokenKind::PpType,
            "spp" => TokenKind::SppType,
            "xspp" => TokenKind::XsppType,
            "p" => TokenKind::PType,
            "nopp" => TokenKind::NoppType,
            "booba" => TokenKind::BoobaType,
            "if" => TokenKind::IfKeyword,
            "else" => TokenKind::ElseKeyword,
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

        Token {
            kind: token_kind,
            row: self.row,
            col: self.col,
            value: Some(buf),
        }
    }
}
