//! The tokenizer for the dpp language.

use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;

#[derive(Debug)]
pub struct Lexer<'a, 'b> {
    /// The raw translation unit input.
    raw_input: &'a str,
    /// The input as a vector of characters because we want to index into it.
    chars: Vec<char>,
    /// The cursor to the chars vector.
    cursor: usize,
    row: u32,
    col: u32,
    error_diag: Arc<RefCell<ErrorDiagnosis<'a, 'b>>>,
}

#[derive(Debug)]
pub struct Token<'a> {
    /// The kind of the token.
    kind: TokenKind,
    /// Row, Column
    position: (u32, u32),
    /// The value of the token. The reason we don't use Option here is because
    /// inside the parser in the method `expect` we return an Option on the value.
    /// If the value is None that means the parser panics - the parsing is stopped,
    /// tokens are consumed until it's synchronized. Note that it does not matter we
    /// use Option there, there could be Result as well.
    value: &'a str,
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ({})", self.value, self.kind)
    }
}

impl<'a> Token<'a> {
    #[must_use]
    pub fn value(&self) -> &'a str {
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
    PprintKeyword, // write()
    PprintlnKeyword, // writeln()
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
            Self::Comment | Self::Whitespace | Self::Eof | Self::Unknown => "",
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
            Self::PprintlnKeyword => "\"pprintln\"",
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
            Self::YarnKeyword => "data type \"yarn\"",
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
        };
        write!(f, "{text_representation}")
    }
}

impl<'a, 'b> Lexer<'a, 'b> {
    /// # Arguments
    ///
    /// * `input`: The translation unit input.
    /// * `error_diag`: The error diagnostics.
    ///
    /// returns: Lexer
    #[must_use]
    pub fn new(input: &'a str, error_diag: Arc<RefCell<ErrorDiagnosis<'a, 'b>>>) -> Self {
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
        Token {
            kind,
            position: (self.row, self.col - 1),
            value,
        }
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
        if matches!(token.kind, TokenKind::Whitespace) || matches!(token.kind, TokenKind::Comment) {
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

    fn advance(&mut self) {
        self.col += 1;
        self.cursor += 1;
    }

    fn handle_p(&mut self) -> Token<'a> {
        let start = self.cursor;

        self.advance(); // Consume opening quote.
        self.advance(); // Consume the character.
        if self.peek() == '\\' {
            // TODO: Handle escaped characters.
            self.advance(); // Consume the escaped character.
        }

        self.advance(); // Consume closing quote.
        self.new_token(
            TokenKind::PKeyword,
            &self.raw_input[start + 1..self.cursor - 1],
        )
    }

    fn handle_unknown(&mut self) -> Token<'a> {
        self.advance();

        self.new_token(
            TokenKind::Unknown,
            &self.raw_input[self.cursor - 1..self.cursor],
        )
    }

    fn handle_comment(&mut self) -> Token<'a> {
        let start = self.cursor;

        self.advance(); // Consume the '#' comment tag.

        while self.peek() != '\n' {
            self.advance();
        }

        self.new_token(TokenKind::Comment, &self.raw_input[start..self.cursor])
    }

    fn handle_operator(&mut self) -> Token<'a> {
        let start = self.cursor;

        match self.peek() {
            '-' => {
                self.advance();
                if self.peek() == '=' || self.peek() == '>' {
                    self.advance();
                }
            }
            '>' | '<' | '!' | '=' | '+' | '*' | '/' | '%' => {
                self.advance();
                if self.peek() == '=' {
                    self.advance();
                }
            }
            _ => {
                self.advance();
            }
        }

        let op = &self.raw_input[start..self.cursor];
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
        self.advance();

        self.new_token(kind, &self.raw_input[self.cursor - 1..self.cursor])
    }

    fn handle_whitespace(&mut self) -> Token<'a> {
        while self.peek().is_whitespace() {
            if self.peek() == '\n' {
                self.row += 1;
                self.col = 1;
            }
            self.advance();
        }

        self.new_token(TokenKind::Whitespace, "")
    }

    fn handle_yarn(&mut self) -> Token<'a> {
        let start = self.cursor;
        self.advance(); // Consume the opening quote.

        while self.peek() != char::default() && self.peek() != '"' && self.peek() != '\n' {
            self.advance(); // Add the character.

            if self.peek() == '\\' {
                self.advance();
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
                self.advance();
            }
        }

        let token = self.new_token(TokenKind::Yarn, &self.raw_input[start + 1..self.cursor]);
        if self.peek() == '"' {
            self.advance(); // Consume the closing quote.
        } else {
            self.error_diag
                .borrow_mut()
                .expected_different_token_error(&token, TokenKind::DoubleQuote);
        }

        token
    }

    fn handle_number(&mut self) -> Token<'a> {
        let start = self.cursor;

        while self.peek().is_ascii_digit() {
            self.advance();
        }

        self.new_token(TokenKind::Number, &self.raw_input[start..self.cursor])
    }

    fn handle_identifier(&mut self) -> Token<'a> {
        let start = self.cursor;

        while self.peek().is_alphabetic() || self.peek() == '_' && !self.peek().is_whitespace() {
            self.advance();
        }

        let ident_value = &self.raw_input[start..self.cursor];
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
