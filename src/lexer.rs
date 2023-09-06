use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub struct SyntaxError {
    row: usize,
    col: usize,
    message: String,
}

impl SyntaxError {
    pub const fn new(row: usize, col: usize, message: String) -> Self {
        Self { row, col, message }
    }
}

#[derive(Debug)]
pub struct UnknownKeywordError {
    pub keyword: String,
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Syntax error at {}:{} - {}",
            self.row, self.col, self.message
        )
    }
}

impl Display for UnknownKeywordError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unknown keyword: {}", self.keyword)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Keyword {
    Xxlpp,
    // u64
    Pp,
    // u32
    Spp,
    // u16
    Xspp,
    // u8
    Let,
    Bye,
    Gfsays,
    Gfyells,
    Func,
}

impl TryFrom<&str> for Keyword {
    type Error = UnknownKeywordError;

    fn try_from(value: &str) -> Result<Self, UnknownKeywordError> {
        match value {
            "xxlpp" => Ok(Self::Xxlpp),
            "pp" => Ok(Self::Pp),
            "spp" => Ok(Self::Spp),
            "xspp" => Ok(Self::Xspp),
            "let" => Ok(Self::Let),
            "gfsays" => Ok(Self::Gfsays),
            "gfyells" => Ok(Self::Gfyells),
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
    tokens: Vec<*const Token>,
}

impl Lexer {
    pub fn new(input: String) -> Self {
        let chars = input.chars().collect();
        Self { chars, position: 0, tokens: Vec::new() }
    }

    pub fn reset(&mut self) {
        self.position = 0;
    }

    pub fn lex(&mut self) -> Result<(), SyntaxError> {
        let mut token = self.next_token()?;
        while token.kind != TokenKind::Eof {
            self.tokens.push(&token);
            token = self.next_token()?;
        }
        Ok(())
    }

    pub fn next_token(&mut self) -> Result<Token, SyntaxError> {
        let token = match self.current_char() {
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
            _ => self.handle_unknown(),
        }?;

        if matches!(token.kind, TokenKind::Whitespace)
            || matches!(token.kind, TokenKind::Comment)
        {
            return self.next_token();
        }
        println!("{token:?}");
        Ok(token)
    }

    fn current_char(&self) -> char {
        if self.position >= self.chars.len() {
            return char::default();
        }

        self.chars[self.position]
    }

    fn next_char(&mut self) -> char {
        self.consume();
        self.current_char()
    }

    fn consume(&mut self) {
        self.position += 1;
    }

    fn handle_unknown(&mut self) -> Result<Token, SyntaxError> {
        let mut buf = String::with_capacity(1);
        buf.push(self.current_char());
        self.consume();

        Ok(Token {
            kind: TokenKind::Unknown,
            value: Some(buf),
        })
    }

    fn handle_comment(&mut self) -> Result<Token, SyntaxError> {
        let mut c = self.next_char();
        while c != '\n' {
            c = self.next_char();
        }

        Ok(Token {
            kind: TokenKind::Comment,
            value: None,
        })
    }

    fn handle_operator(&mut self) -> Result<Token, SyntaxError> {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(2);
        buf.push(c);

        c = self.next_char();
        if "+-*/%^=<>!&|~".contains(c) {
            buf.push(c);
            self.consume();
        }

        Ok(Token {
            kind: TokenKind::Operator,
            value: Some(buf),
        })
    }

    fn handle_punctuation(&mut self) -> Result<Token, SyntaxError> {
        let c = self.current_char();
        self.consume();
        let mut buf = String::with_capacity(1);
        buf.push(c);

        Ok(Token {
            kind: TokenKind::Punctuation,
            value: Some(buf),
        })
    }

    fn handle_whitespace(&mut self) -> Result<Token, SyntaxError> {
        let mut c = self.next_char();
        while c.is_whitespace() || c == '\r' {
            c = self.next_char();
        }

        Ok(Token {
            kind: TokenKind::Whitespace,
            value: None,
        })
    }

    fn handle_string(&mut self) -> Result<Token, SyntaxError> {
        let mut buf = String::with_capacity(256);

        let mut c = self.next_char();
        while c != char::default() && c != '"' {
            buf.push(c);
            c = self.next_char();
            if c == '\\' {
                buf.push(c);
                c = self.next_char();
            }
        }
        // Consume the closing quote.
        self.consume();

        Ok(Token {
            kind: TokenKind::String,
            value: Some(buf),
        })
    }

    fn handle_number(&mut self) -> Result<Token, SyntaxError> {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(256);
        buf.push(c);

        c = self.next_char();
        while c.is_ascii_digit() {
            buf.push(c);
            c = self.current_char();
        }

        Ok(Token {
            kind: TokenKind::Number,
            value: Some(buf),
        })
    }

    fn handle_identifier(&mut self) -> Result<Token, SyntaxError> {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(256);
        buf.push(c);

        c = self.next_char();
        while c.is_alphabetic() || c == '_' && !c.is_whitespace() {
            buf.push(c);
            c = self.next_char();
        }

        Ok(Token {
            kind: Keyword::try_from(buf.as_str())
                .map_or(TokenKind::Identifier, |_| TokenKind::Keyword),
            value: Some(buf),
        })
    }
}
