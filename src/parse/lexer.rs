//! The tokenizer for the dpp language.

use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;

#[derive(Debug)]
pub struct Lexer<'a> {
    // TODO: This could be a string slice.
    raw_input: &'a str,
    chars: Vec<char>,
    position: usize,
    row: u32,
    col: u32,
    error_diag: Arc<RefCell<ErrorDiagnosis>>,
}

#[derive(Debug)]
pub struct Token<'a> {
    kind: TokenKind,
    /// Row, Column
    position: (u32, u32),
    value: Option<&'a str>,
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

impl Display for Token<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(value) = &self.value {
            write!(f, "{} ({})", value, self.kind)
        } else {
            write!(f, "\"{}\"", self.kind)
        }
    }
}

impl<'a> Token<'a> {
    #[must_use]
    pub fn value(&self) -> Option<&'a str> {
        self.value
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
    Yarn,
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
    FUNcKeyword,   // function
    PprintKeyword, // print()
    PpanicKeyword, // panic()
    PpinKeyword,   // read()
    XxlppKeyword,  // i64
    PpKeyword,     // i32
    SppKeyword,    // i16
    XsppKeyword,   // i8
    PKeyword,      // char
    BoobaKeyword,  // bool
    NoppKeyword,   // void
    YarnKeyword,   // String
    ForKeyword,
    ElseKeyword,
    DoubleQuote,
    ToKeyword,
    Arrow,
    WhileKeyword,
    DoKeyword,
    LoopKeyword,
    BreakKeyword,
    ContinueKeyword,
    CaseKeyword,
    SwitchKeyword,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let text_representation = match self {
            Self::Identifier => "identifier",
            Self::Number => "number",
            Self::Yarn => "yarn",
            Self::BangEqual => "\"!=\"",
            Self::Comment => "",
            Self::Whitespace => "",
            Self::Eof => "",
            Self::Unknown => "",
            Self::EqualEqual => "\"==\"",
            Self::Equal => "\"=\"",
            Self::Bang => "\"!\"",
            Self::Star => "\"*\"",
            Self::ForwardSlash => "\"/\"",
            Self::BackSlash => "\"\\\"",
            Self::Plus => "\"+\"",
            Self::MinusEqual => "\"-=\"",
            Self::PlusEqual => "\"+=\"",
            Self::PlusDash => "\"+-\"",
            Self::Dash => "\"-\"",
            Self::Greater => "\">\"",
            Self::GreaterEqual => "\">=\"",
            Self::Less => "\"<\"",
            Self::LessEqual => "\"<=\"",
            Self::NomKeyword => "\"nom\"",
            Self::YemKeyword => "\"yem\"",
            Self::OpenParen => "\"(\"",
            Self::CloseParen => "\")\"",
            Self::OpenBrace => "\"{\"",
            Self::CloseBrace => "\"}\"",
            Self::OpenBracket => "\"[\"",
            Self::CloseBracket => "\"]\"",
            Self::Colon => "\":\"",
            Self::Semicolon => "\";\"",
            Self::Ampersand => "\"&\"",
            Self::Pipe => "\"|\"",
            Self::Comma => "\",\"",
            Self::IfKeyword => "\"if\"",
            Self::LetKeyword => "\"let\"",
            Self::ByeKeyword => "\"bye\"",
            Self::PprintKeyword => "\"pprint\"",
            Self::PpanicKeyword => "\"ppanic\"",
            Self::PpinKeyword => "\"ppin\"",
            Self::FUNcKeyword => "\"FUNc\"",
            Self::ElseKeyword => "\"else\"",
            Self::ForKeyword => "\"for\"",
            Self::XxlppKeyword => "data type \"xxlpp\"",
            Self::PpKeyword => "data type \"pp\"",
            Self::SppKeyword => "data type \"spp\"",
            Self::XsppKeyword => "data type \"xspp\"",
            Self::PKeyword => "data type \"p\"",
            Self::BoobaKeyword => "data type \"booba\"",
            Self::NoppKeyword => "void data type \"nopp\"",
            Self::DoubleQuote => "\"\"\"",
            Self::ToKeyword => "\"to\"",
            Self::Arrow => "\"->\"",
            Self::WhileKeyword => "\"while\"",
            Self::DoKeyword => "\"do\"",
            Self::LoopKeyword => "\"loop\"",
            Self::BreakKeyword => "\"break\"",
            Self::ContinueKeyword => "\"continue\"",
            Self::SwitchKeyword => "\"switch\"",
            Self::CaseKeyword => "\"case\"",
            Self::YarnKeyword => "\"yarn\"",
        };
        write!(f, "{text_representation}")
    }
}

impl<'a> Lexer<'a> {
    #[must_use]
    pub fn new(input: &'a str, error_diag: Arc<RefCell<ErrorDiagnosis>>) -> Self {
        // Create a vector of characters from the input string. This is so that we can access the
        // characters by index. Unfortunately this will take up more memory than necessary as we
        // will pass in the Token struct a String instead of a string slice.
        let chars = input.chars().collect();
        Self {
            raw_input: input,
            chars,
            position: 0,
            row: 1,
            col: 1,
            error_diag,
        }
    }

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
        Token {
            kind,
            position: (self.row, self.col),
            value: Some(value),
        }
    }

    fn parse_token(&mut self) -> Token<'a> {
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

    fn str_slice(&self, len: usize) -> &'a str {
        &self.raw_input[self.position..self.position + len]
    }

    fn handle_p(&mut self) -> Token<'a> {
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
        self.new_token(TokenKind::PKeyword, self.str_slice(1))
    }

    fn handle_unknown(&mut self) -> Token<'a> {
        self.consume();

        self.new_token(TokenKind::Unknown, self.str_slice(1))
    }

    fn handle_comment(&mut self) -> Token<'a> {
        let start = self.position;
        // Consume the comment tag
        self.consume();

        let mut c = self.peek();
        while c != '\n' {
            self.consume();
            c = self.peek();
        }

        self.new_token(TokenKind::Comment, &self.raw_input[start..self.position])
    }

    fn handle_operator(&mut self) -> Token<'a> {
        let operator_start = self.position;
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

        self.new_token(kind, &self.raw_input[operator_start..self.position])
    }

    fn handle_punctuation(&mut self) -> Token<'a> {
        let punctuation_start = self.position;
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

        self.new_token(kind, &self.raw_input[punctuation_start..self.position])
    }

    fn handle_whitespace(&mut self) -> Token<'a> {
        let mut c = self.peek();
        while c.is_whitespace() {
            self.consume();
            if c == '\n' {
                self.row += 1;
                self.col = 1;
            }
            c = self.peek();
        }

        self.new_token(TokenKind::Whitespace, "")
    }

    fn handle_yarn(&mut self) -> Token<'a> {
        const MAX_YARN_LEN: usize = 256;
        let mut buf = String::with_capacity(256);

        // Consume the opening quote.
        self.consume();

        // Set the start of the yarn (String) to right after the opening quote.
        let yarn_start = self.position;

        let mut c = self.peek();
        while c != char::default() && c != '"' && c != '\n' {
            buf.push(c);
            self.consume();
            c = self.peek();

            if c == '\\' {
                self.consume();
                let x = match self.peek() {
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
                buf.push(x);
                self.consume();
                c = self.peek();
            }
        }

        if c == '"' {
            // Consume the closing quote.
            self.consume();
        }

        let token = self.new_token(
            TokenKind::Yarn,
            &self.raw_input[yarn_start..self.position - 1],
        );

        if c != '"' {
            self.error_diag
                .borrow_mut()
                .expected_different_token_error(&token, TokenKind::DoubleQuote);
        }

        token
    }

    fn handle_number(&mut self) -> Token<'a> {
        let number_start = self.position;

        let mut c = self.peek();
        while c.is_ascii_digit() {
            self.consume();
            c = self.peek();
        }

        self.new_token(
            TokenKind::Number,
            &self.raw_input[number_start..self.position],
        )
    }

    fn handle_identifier(&mut self) -> Token<'a> {
        let identifier_start = self.position;
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

        self.new_token(kind, &self.raw_input[identifier_start..self.position])
    }
}
