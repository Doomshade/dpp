pub enum Keywords {
    Pp,
    Bigpp,
    Smolpp,
    Let,
    Gfsays,
    Gfyells,
}

pub struct UnknownKeywordError;

impl TryFrom<&str> for Keywords {
    type Error = UnknownKeywordError;

    fn try_from(value: &str) -> Result<Self, UnknownKeywordError> {
        match value {
            "pp" => Ok(Keywords::Pp),
            "bigpp" => Ok(Keywords::Bigpp),
            "smolpp" => Ok(Keywords::Smolpp),
            "let" => Ok(Keywords::Let),
            "gfsays" => Ok(Keywords::Gfsays),
            "gfyells" => Ok(Keywords::Gfyells),
            _ => Err(UnknownKeywordError),
        }
    }
}

#[derive(Debug)]
pub struct Token {
    kind: TokenKind,
    value: Option<String>,
}

#[derive(Debug)]
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

#[derive(Debug)]
#[derive(Default)]
pub struct Lexer<'a> {
    input: &'a str,
    chars: Vec<char>,
    position: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        let chars = input.chars().collect();
        Lexer {
            input,
            chars,
            position: 0,
        }
    }

    pub fn lex(&mut self) {
        loop {
            if matches!(self.next_token().kind, TokenKind::Eof) {
                break;
            }
        }
    }

    fn next_token(&mut self) -> Token {
        let (buf, token_kind) = match self.current_char() {
            '\0' => (None, TokenKind::Eof),
            'a'..='z' | 'A'..='Z' | '_' => self.handle_identifier(),
            '0'..='9' => self.handle_number(),
            '"' => self.handle_string(),
            ' ' | '\t' | '\n' | '\r' => self.handle_whitespace(),
            ';' | '(' | ')' | '{' | '}' | ',' | '[' | ']' | ':' => self.handle_punctuation(),
            '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '~' =>
                self.handle_operator(),
            '#' => self.handle_comment(),
            _ => self.handle_unknown(),
        };

        let token = Token {
            kind: token_kind,
            value: buf,
        };

        if matches!(token.kind, TokenKind::Whitespace) || matches!(token.kind, TokenKind::Comment) {
            return self.next_token();
        }
        println!("{:?}", token);

        token
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

    fn handle_unknown(&mut self) -> (Option<String>, TokenKind) {
        let mut buf = String::with_capacity(1);
        buf.push(self.current_char());
        self.consume();

        (Some(buf), TokenKind::Unknown)
    }

    fn handle_comment(&mut self) -> (Option<String>, TokenKind) {
        let mut buf = String::with_capacity(256);
        let mut c = self.next_char();
        while c != '\n' {
            buf.push(c);
            c = self.current_char();
        }

        (Some(buf), TokenKind::Comment)
    }

    fn handle_operator(&mut self) -> (Option<String>, TokenKind) {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(2);
        buf.push(c);

        c = self.next_char();
        if "+-*/%^=<>!&|~".contains(c) {
            buf.push(c);
            self.consume();
        }

        (Some(buf), TokenKind::Operator)
    }

    fn handle_punctuation(&mut self) -> (Option<String>, TokenKind) {
        let c = self.current_char();
        self.consume();
        let mut buf = String::with_capacity(1);
        buf.push(c);

        (Some(buf), TokenKind::Punctuation)
    }

    fn handle_whitespace(&mut self) -> (Option<String>, TokenKind) {
        let mut c = self.next_char();
        while c.is_whitespace() || c == '\r' {
            c = self.next_char();
        }

        (None, TokenKind::Whitespace)
    }

    fn handle_string(&mut self) -> (Option<String>, TokenKind) {
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

        (Some(buf), TokenKind::String)
    }

    fn handle_number(&mut self) -> (Option<String>, TokenKind) {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(256);
        buf.push(c);

        c = self.next_char();
        while c.is_ascii_digit() {
            buf.push(c);
            c = self.current_char();
        }

        (Some(buf), TokenKind::Number)
    }

    fn handle_identifier(&mut self) -> (Option<String>, TokenKind) {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(256);
        buf.push(c);

        c = self.next_char();
        while c.is_alphabetic() || c == '_' && !c.is_whitespace() {
            buf.push(c);
            c = self.next_char();
        }

        let kind = Keywords::try_from(buf.as_str()).map_or(TokenKind::Identifier, |_|
            TokenKind::Keyword);
        (Some(buf), kind)
    }
}
