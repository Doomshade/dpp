use std::fmt::{Display, Formatter};

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

impl TryFrom<&str> for DataType {
    type Error = UnknownDataTypeError;

    fn try_from(value: &str) -> Result<Self, UnknownDataTypeError> {
        match value {
            "xxlpp" => Ok(Self::Xxlpp),
            "pp" => Ok(Self::Pp),
            "spp" => Ok(Self::Spp),
            "xspp" => Ok(Self::Xspp),
            "nopp" => Ok(Self::Nopp),
            "thread" => Ok(Self::Thread),
            "boob" => Ok(Self::Boob),
            "p" => Ok(Self::P),
            _ => Err(UnknownDataTypeError {
                keyword: String::from(value),
            }),
        }
    }
}

impl TryFrom<&str> for Keyword {
    type Error = UnknownKeywordError;

    fn try_from(value: &str) -> Result<Self, UnknownKeywordError> {
        match value {
            "let" => Ok(Self::Let),
            "pprint" => Ok(Self::Pprint),
            "ppanic" => Ok(Self::Ppanic),
            "ppin" => Ok(Self::Ppin),
            "bye" => Ok(Self::Bye),
            "FUNc" => Ok(Self::Func),
            _ => Err(UnknownKeywordError {
                keyword: String::from(value),
            }),
        }
    }
}

#[derive(Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub value: Option<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
    Identifier,
    Number,
    String,
    Character,
    Operator,
    Punctuation,
    Keyword,
    Comment,
    Whitespace,
    Eof,
    Unknown,
}

#[derive(Debug, Default)]
pub struct Lexer {
    chars: Vec<char>,
    position: usize,
    tokens: Vec<Token>,
    curr_token_index: usize,
    row: usize,
    col: usize,
}

impl Lexer {
    pub const fn tokens(&self) -> &Vec<Token> {
        &self.tokens
    }

    pub fn new(input: &str) -> Self {
        let chars = input.chars().collect();
        Self {
            chars,
            position: 0,
            tokens: Vec::new(),
            curr_token_index: 0,
            row: 0,
            col: 0,
        }
    }

    pub fn reset(&mut self) {
        self.tokens.clear();
        self.row = 0;
        self.col = 0;
        self.curr_token_index = 0;
        self.position = 0;
    }

    pub fn lex(&mut self) -> Result<(), SyntaxError> {
        let mut token = self.parse_token()?;
        while token.kind != TokenKind::Eof {
            self.tokens.push(token);
            token = self.parse_token()?;
        }
        Ok(())
    }

    pub fn consume_token(&mut self) {
        self.curr_token_index += 1;
    }

    pub fn token(&self) -> Option<&Token> {
        self.token_lookahead(0)
    }

    pub fn token_lookahead(&self, ahead: usize) -> Option<&Token> {
        if self.curr_token_index + ahead >= self.tokens.len() {
            return None;
        }
        Some(&self.tokens[self.curr_token_index + ahead])
    }

    fn parse_token(&mut self) -> Result<Token, SyntaxError> {
        let token = match self.peek() {
            '\0' => Ok(Token {
                kind: TokenKind::Eof,
                value: None,
            }),
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
        }?;

        if matches!(token.kind, TokenKind::Whitespace)
            || matches!(token.kind, TokenKind::Comment)
        {
            return self.parse_token();
        }
        dbg!(&token);
        Ok(token)
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

    fn handle_char(&mut self) -> Result<Token, SyntaxError> {
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
        Ok(Token {
            kind: TokenKind::Character,
            value: Some(String::from(c)),
        })
    }

    fn handle_unknown(&mut self) -> Result<Token, SyntaxError> {
        let c = self.peek();
        self.consume();

        Ok(Token {
            kind: TokenKind::Unknown,
            value: Some(String::from(c)),
        })
    }

    fn handle_comment(&mut self) -> Result<Token, SyntaxError> {
        // Consume the comment tag
        self.consume();

        let mut c = self.peek();
        while c != '\n' {
            self.consume();
            c = self.peek();
        }

        Ok(Token {
            kind: TokenKind::Comment,
            value: None,
        })
    }


    fn handle_operator(&mut self) -> Result<Token, SyntaxError> {
        let c = self.peek();
        self.consume();

        Ok(Token {
            kind: TokenKind::Operator,
            value: Some(String::from(c)),
        })
    }

    fn handle_punctuation(&mut self) -> Result<Token, SyntaxError> {
        let c = self.peek();
        self.consume();

        Ok(Token {
            kind: TokenKind::Punctuation,
            value: Some(String::from(c)),
        })
    }

    fn handle_whitespace(&mut self) -> Result<Token, SyntaxError> {
        let mut c = self.peek();
        while c.is_whitespace() || c == '\r' {
            self.consume();
            c = self.peek();
        }

        Ok(Token {
            kind: TokenKind::Whitespace,
            value: None,
        })
    }

    fn handle_string(&mut self) -> Result<Token, SyntaxError> {
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
            return Err(SyntaxError {
                file: file!().to_string(),
                row: line!() as usize,
                col: column!() as usize,
                message: String::from("Missing end of string"),
            });
        }
        // Consume the closing quote.
        self.consume();

        Ok(Token {
            kind: TokenKind::String,
            value: Some(buf),
        })
    }

    fn handle_number(&mut self) -> Result<Token, SyntaxError> {
        let mut buf = String::with_capacity(256);

        let mut c = self.peek();
        while c.is_ascii_digit() {
            buf.push(c);
            self.consume();
            c = self.peek();
        }

        Ok(Token {
            kind: TokenKind::Number,
            value: Some(buf),
        })
    }

    fn is_keyword(identifier: &str) -> bool {
        matches!(identifier, "xxlpp" | "pp" | "spp" | "xspp" | "p" | "nopp" | "boob" | "let" | "bye" | "pprint" | "ppanic" | "ppin" | "FUNc")
    }

    fn handle_identifier(&mut self) -> Result<Token, SyntaxError> {
        let mut buf = String::with_capacity(256);

        let mut c = self.peek();
        while c.is_alphabetic() || c == '_' && !c.is_whitespace() {
            buf.push(c);
            self.consume();
            c = self.peek();
        }
        let token_kind = if Self::is_keyword(buf.as_str()) {
            TokenKind::Keyword
        } else {
            TokenKind::Identifier
        };

        Ok(Token {
            kind: token_kind,
            value: Some(buf),
        })
    }
}
