/// For each declaration in grammar we declare an enum and a function that parses that declaration.
///
/// Each enum always consists of a default variant, usually prefixed by "Invalid" that allows us to
/// continue parsing even though an error occurred. That way we are able to insert a placeholder
/// in the AST and continue parsing. This is useful for error recovery.
///
/// Each enum also contains a variant for each possible production in the grammar,
/// usually defaulting to one variant with the same name (e.g. Function::Function). This adds a
/// little bit of boilerplate, but it allows us to easily add new productions to the grammar.
///
/// Each enum also derives Debug that lets us print the tree structure of the AST.\
mod lexer;
mod parser;

use crate::error_diagnosis::ErrorDiagnosis;
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::sync::Arc;

#[derive(Debug)]
pub struct Lexer {
    // TODO: This could be a string slice.
    chars: Vec<char>,
    position: usize,
    row: u32,
    col: u32,
    error_diag: Arc<RefCell<ErrorDiagnosis>>,
}

#[derive(Debug)]
pub struct Token {
    kind: TokenKind,
    /// Row, Column
    position: (u32, u32),
    value: Option<String>,
}
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
    XxlppKeyword,  // u64
    PpKeyword,     // u32
    SppKeyword,    // u16
    XsppKeyword,   // u8
    PKeyword,      // char
    BoobaKeyword,  // bool
    Yarn,          // String
    NoppKeyword,   // Void
    YarnKeyword,   // String keyword
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
            Self::XxlppKeyword => "data type \"xxlpp\"",
            Self::PpKeyword => "data type \"pp\"",
            Self::SppKeyword => "data type \"spp\"",
            Self::XsppKeyword => "data type \"xspp\"",
            Self::PKeyword => "data type \"p\"",
            Self::BoobaKeyword => "data type \"booba\"",
            Self::NoppKeyword => "void data type \"nopp\"",
            Self::DoubleQuote => "\"\"\"",
            Self::ToKeyword => "to",
            Self::Arrow => "->",
            Self::WhileKeyword => "while",
            Self::DoKeyword => "do",
            Self::LoopKeyword => "loop",
            Self::BreakKeyword => "break",
            Self::ContinueKeyword => "continue",
            Self::SwitchKeyword => "switch",
            Self::CaseKeyword => "case",
            Self::YarnKeyword => "yarn",
        };
        write!(f, "{text_representation}")
    }
}

#[derive(Debug)]
pub struct Parser {
    tokens: Arc<Vec<Token>>,
    error_diag: Arc<RefCell<ErrorDiagnosis>>,
    curr_token_index: usize,
    position: (u32, u32),
    error: bool,
}

#[derive(Debug)]
pub struct TranslationUnit {
    pub functions: Vec<Function>,
    pub variables: Vec<Statement>,
}

#[derive(Debug)]
pub struct Function {
    pub position: (u32, u32),
    pub identifier: String,
    pub return_type: DataType,
    pub parameters: Vec<Parameter>,
    pub block: Block,
}

#[derive(Debug)]
pub struct Parameters {
    position: (u32, u32),
    parameters: Vec<Parameter>,
}

#[derive(Debug)]
pub struct Parameter {
    position: (u32, u32),
    identifier: String,
    data_type: DataType,
}

#[derive(Debug)]
pub struct Block {
    pub position: (u32, u32),
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Statement {
    VariableDeclaration {
        position: (u32, u32),
        identifier: String,
        data_type: DataType,
    },
    VariableDeclarationAndAssignment {
        position: (u32, u32),
        identifier: String,
        data_type: DataType,
        expression: Expression,
    },
    IfStatement {
        position: (u32, u32),
        expression: Expression,
        statement: Box<Statement>,
    },
    IfElseStatement {
        position: (u32, u32),
        expression: Expression,
        statement: Box<Statement>,
        else_statement: Box<Statement>,
    },
    ReturnStatement {
        position: (u32, u32),
        expression: Expression,
    },
    BlockStatement {
        position: (u32, u32),
        block: Box<Block>,
    },
    ExpressionStatement {
        position: (u32, u32),
        expression: Expression,
    },
    EmptyStatement {
        position: (u32, u32),
    },
    ForStatement {
        position: (u32, u32),
        index_ident: String,
        length_expression: Expression,
        statement: Box<Statement>,
    },
    ForStatementWithIdentExpression {
        position: (u32, u32),
        ident: Expression,
        length_expression: Expression,
        statement: Box<Statement>,
    },
    WhileStatement {
        position: (u32, u32),
        expression: Expression,
        statement: Box<Statement>,
    },
    DoWhileStatement {
        position: (u32, u32),
        block: Block,
        expression: Expression,
    },
    LoopStatement {
        position: (u32, u32),
        block: Box<Block>,
    },
    BreakStatement {
        position: (u32, u32),
    },
    ContinueStatement {
        position: (u32, u32),
    },
    SwitchStatement {
        position: (u32, u32),
        expression: Expression,
        cases: Vec<Case>,
    },
}

#[derive(Debug)]
pub struct Case {
    expression: Expression,
    block: Box<Block>,
}

#[derive(Debug)]
pub enum Expression {
    PpExpression {
        position: (u32, u32),
        pp: i32,
    },
    BoobaExpression {
        position: (u32, u32),
        booba: bool,
    },
    YarnExpression {
        position: (u32, u32),
        yarn: String,
    },
    UnaryExpression {
        position: (u32, u32),
        op: UnaryOperator,
        operand: Box<Expression>,
    },
    BinaryExpression {
        position: (u32, u32),
        lhs: Box<Expression>,
        op: BinaryOperator,
        rhs: Box<Expression>,
    },
    IdentifierExpression {
        position: (u32, u32),
        identifier: String,
    },
    FunctionCall {
        position: (u32, u32),
        identifier: String,
        arguments: Vec<Expression>,
    },
    AssignmentExpression {
        position: (u32, u32),
        identifier: String,
        expression: Box<Expression>,
    },
    InvalidExpression,
}

#[derive(Debug, Eq, PartialEq)]
pub enum DataType {
    // u64
    Xxlpp,
    // u32
    Pp,
    // u16
    Spp,
    // u8
    Xspp,
    // char
    P,
    // string
    Yarn,
    // bool
    Booba,
    // void
    Nopp,
    Struct { name: String },
}

#[derive(Debug)]
pub struct Struct {}

#[derive(Debug)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    NotEqual,
    Equal,
    GreaterThan,
    GreaterThanOrEqual,
    LessThan,
    LessThanOrEqual,
}

#[derive(Debug)]
pub enum UnaryOperator {
    Not,
    Negate,
}
