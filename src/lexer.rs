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
    Keyword,
    Operator,
    Punctuation,
    Comment,
    Whitespace,
    Newline,
    Eof,
    Unknown,
}

#[derive(Debug)]
#[derive(Default)]
pub struct Lexer {
    chars: Vec<char>,
    position: usize,
}

impl Lexer {
    fn next(&mut self) -> Token {
        unimplemented!("next")
    }

    fn peek(&mut self) -> Token {
        self.peek_ahead(0usize)
    }

    fn peek_ahead(&mut self, _ahead: usize) -> Token {
        unimplemented!("peek_ahead")
    }

    pub fn lex(&mut self, input: &str) -> Vec<Token> {
        let mut input = String::from(input);
        input.push('\n');

        self.position = 0;
        self.chars = input.chars().collect();

        let mut tokens: Vec<Token> = Vec::new();
        loop {
            let c = self.current_char();
            if c == char::default() {
                let eof = Token { kind: TokenKind::Eof, value: None };
                println!("{:?}", eof);
                tokens.push(eof);
                break;
            }

            let (buf, token_kind) = match c {
                'a'..='z' | 'A'..='Z' | '_' => self.handle_identifier(),
                '0'..='9' => self.handle_number(),
                '"' => self.handle_string(),
                ' ' | '\t' | '\n' | '\r' => self.handle_whitespace(),
                ';' | '(' | ')' | '{' | '}' | ',' | '[' | ']' => self.handle_punctuation(),
                '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '~' =>
                    self.handle_operator(),
                '#' => self.handle_comment(),
                _ => self.handle_unknown(),
            };

            let token = Token {
                kind: token_kind.unwrap_or(TokenKind::Unknown),
                value: buf,
            };

            if !matches!(token.kind, TokenKind::Whitespace) && !matches!(token.kind,
                TokenKind::Comment) {
                println!("{:?}", token);
                tokens.push(token);
            }
        }

        tokens
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

    fn previous_char(&mut self) -> char {
        self.position -= 1;
        self.current_char()
    }

    fn handle_unknown(&mut self) -> (Option<String>, Option<TokenKind>) {
        let mut buf = String::with_capacity(1);
        buf.push(self.current_char());
        self.consume();

        (Some(buf), Some(TokenKind::Unknown))
    }

    fn handle_comment(&mut self) -> (Option<String>, Option<TokenKind>) {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(256);
        buf.push(c);

        c = self.current_char();
        while c != '\n' {
            buf.push(c);
            c = self.current_char();
        }

        (Some(buf), Some(TokenKind::Comment))
    }

    fn handle_operator(&mut self) -> (Option<String>, Option<TokenKind>) {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(2);
        buf.push(c);

        c = self.next_char();
        if "+-*/%^=<>!&|~".contains(c) {
            buf.push(c);
            self.consume();
        }

        (Some(buf), Some(TokenKind::Operator))
    }

    fn handle_punctuation(&mut self) -> (Option<String>, Option<TokenKind>) {
        let c = self.current_char();
        self.consume();
        let mut buf = String::with_capacity(1);
        buf.push(c);

        (Some(buf), Some(TokenKind::Punctuation))
    }

    fn handle_whitespace(&mut self) -> (Option<String>, Option<TokenKind>) {
        let mut c = self.current_char();

        c = self.next_char();

        while c.is_whitespace() || c == '\r' {
            c = self.next_char();
        }

        (None, Some(TokenKind::Whitespace))
    }

    fn handle_string(&mut self) -> (Option<String>, Option<TokenKind>) {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(256);

        c = self.next_char();
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

        (Some(buf), Some(TokenKind::String))
    }

    fn handle_number(&mut self) -> (Option<String>, Option<TokenKind>) {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(256);
        buf.push(c);

        c = self.next_char();
        while c.is_ascii_digit() {
            buf.push(c);
            c = self.current_char();
        }

        (Some(buf), Some(TokenKind::Number))
    }

    fn handle_identifier(&mut self) -> (Option<String>, Option<TokenKind>) {
        let mut c = self.current_char();
        let mut buf = String::with_capacity(256);
        buf.push(c);

        c = self.next_char();
        while c.is_alphabetic() || c == '_' && !c.is_whitespace() {
            buf.push(c);
            c = self.next_char();
        }

        (Some(buf), Some(TokenKind::Identifier))
    }
}
