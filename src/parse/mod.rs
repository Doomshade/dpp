use dpp_macros_derive::PosMacro;
use dpp_macros::PosMacro;
use std::fmt::{Display, Formatter};
use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::parser::{BinaryOperator, Number, Statement, UnaryOperator};

pub mod analysis;
pub mod lexer;
pub mod parser;

#[derive(Clone, Debug, PosMacro)]
pub struct TranslationUnit<'a> {
    position: (u32, u32),
    functions: Vec<Function<'a>>,
    global_statements: Vec<Statement<'a>>,
}

impl<'a> TranslationUnit<'a> {
    pub fn new(functions: Vec<Function<'a>>,
               global_statements: Vec<Statement<'a>>) -> Self {
        TranslationUnit {
            position: (1, 1),
            functions,
            global_statements,
        }
    }

    pub fn functions(&self) -> &Vec<Function<'a>> {
        &self.functions
    }
    pub fn global_statements(&self) -> &Vec<Statement<'a>> {
        &self.global_statements
    }
}

#[derive(Clone, Debug, PosMacro)]
pub struct Function<'a> {
    position: (u32, u32),
    identifier: &'a str,
    return_type: DataType<'a>,
    parameters: Vec<Variable<'a>>,
    block: Block<'a>,
}

impl<'a> Function<'a> {
    pub fn new(
        position: (u32, u32),
        identifier: &'a str,
        return_type: DataType<'a>,
        parameters: Vec<Variable<'a>>,
        block: Block<'a>,
    ) -> Self {
        Function {
            position,
            identifier,
            return_type,
            parameters,
            block,
        }
    }

    pub fn identifier(&self) -> &'a str {
        self.identifier
    }
    pub fn return_type(&self) -> &DataType<'a> {
        &self.return_type
    }
    pub fn block(&self) -> &Block<'a> {
        &self.block
    }
    pub fn parameters(&self) -> &Vec<Variable<'a>> {
        &self.parameters
    }

    /// The size of parameters in instructions.
    pub fn parameters_size(&self) -> usize {
        self.parameters().iter().fold(0, |acc, parameter| {
            acc + parameter.data_type().size_in_instructions()
        })
    }
}

#[derive(Clone, Debug)]
pub struct Block<'a> {
    position: (u32, u32),
    statements: Vec<Statement<'a>>,
}

impl<'a> Block<'a> {
    pub fn new(position: (u32, u32), statements: Vec<Statement<'a>>) -> Self {
        Block {
            position,
            statements,
        }
    }

    pub fn position(&self) -> (u32, u32) {
        self.position
    }
    pub fn statements(&self) -> &Vec<Statement<'a>> {
        &self.statements
    }
}

#[derive(Clone, Debug)]
pub struct Variable<'a> {
    position: (u32, u32),
    position_in_scope: Option<u32>,
    identifier: &'a str,
    data_type: DataType<'a>,
    size: usize,
    value: Option<Expression<'a>>,
}

impl<'a> Variable<'a> {
    pub fn new(
        position: (u32, u32),
        identifier: &'a str,
        data_type: DataType<'a>,
        value: Option<Expression<'a>>,
    ) -> Self {
        Variable {
            position,
            position_in_scope: None,
            identifier,
            size: data_type.size(),
            data_type,
            value,
        }
    }

    pub fn position(&self) -> (u32, u32) {
        self.position
    }
    pub fn position_in_scope(&self) -> Option<u32> {
        self.position_in_scope
    }
    pub fn identifier(&self) -> &'a str {
        self.identifier
    }
    pub fn data_type(&self) -> &DataType<'a> {
        &self.data_type
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn value(&self) -> Option<&Expression<'a>> {
        self.value.as_ref()
    }

    pub fn set_position_in_scope(&mut self, position_in_scope: u32) {
        self.position_in_scope = Some(position_in_scope);
    }

    pub fn size_in_instructions(&self) -> usize {
        ((self.size() - 1) / 4) + 1
    }
}

#[derive(Clone, Debug)]
pub enum Expression<'a> {
    // TODO: Use LiteralExpression instead.
    Number {
        position: (u32, u32),
        number_type: Number,
        value: i32,
    },
    P {
        position: (u32, u32),
        value: char,
    },
    Booba {
        position: (u32, u32),
        value: bool,
    },
    Yarn {
        position: (u32, u32),
        value: &'a str,
    },
    Unary {
        position: (u32, u32),
        op: UnaryOperator,
        operand: Box<Expression<'a>>,
    },
    Binary {
        position: (u32, u32),
        lhs: Box<Expression<'a>>,
        op: BinaryOperator,
        rhs: Box<Expression<'a>>,
    },
    Identifier {
        position: (u32, u32),
        identifier: &'a str,
    },
    FunctionCall {
        position: (u32, u32),
        identifier: &'a str,
        arguments: Vec<Expression<'a>>,
    },
    Assignment {
        position: (u32, u32),
        identifier: &'a str,
        expression: Box<Expression<'a>>,
    },
    Invalid,
}

impl Display for Expression<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let formatted = match self {
            Expression::Number { value, .. } => value.to_string(),
            Expression::P { value, .. } => value.to_string(),
            Expression::Booba { value, .. } => value.to_string(),
            Expression::Yarn { value, .. } => value.to_string(),
            Expression::Unary { operand, .. } => "Unary expression".to_string(),
            Expression::Binary { .. } => "Binary expression".to_string(),
            Expression::Identifier { identifier, .. } => identifier.to_string(),
            Expression::FunctionCall { identifier, .. } => {
                format!("Function {}", identifier)
            }
            Expression::Assignment { identifier, .. } => identifier.to_string(),
            Expression::Invalid => "Invalid expression".to_string(),
        };
        write!(f, "{}", formatted)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum DataType<'a> {
    // Xxlpp, Pp, Spp, Xspp
    Number(Number),
    // char
    P,
    // string
    Yarn,
    // bool
    Booba,
    // void
    Nopp,
    Struct { name: &'a str },
}

impl PartialEq for DataType<'_> {
    fn eq(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (DataType::Number(..), DataType::Number(..))
                | (DataType::P, DataType::P)
                | (DataType::Yarn, DataType::Yarn)
                | (DataType::Booba, DataType::Booba)
                | (DataType::Nopp, DataType::Nopp)
        )
    }
}

impl Display for DataType<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            DataType::Number(_) => write!(f, "number")?,
            DataType::P => write!(f, "p")?,
            DataType::Yarn => write!(f, "yarn")?,
            DataType::Booba => write!(f, "booba")?,
            DataType::Nopp => write!(f, "nopp")?,
            DataType::Struct { name } => write!(f, "struct {name}")?,
        };

        Ok(())
    }
}

impl<'a> DataType<'a> {
    pub fn size(&self) -> usize {
        match self {
            DataType::Number(number) => match number {
                Number::Pp => std::mem::size_of::<i32>(),
                Number::Spp => std::mem::size_of::<i16>(),
                Number::Xspp => std::mem::size_of::<i8>(),
            },
            DataType::P => std::mem::size_of::<char>(),
            DataType::Booba => std::mem::size_of::<bool>(),
            _ => panic!("Invalid data type"),
        }
    }

    pub fn size_in_instructions(&self) -> usize {
        ((self.size() - 1) / 4) + 1
    }
}

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
    error_diag: std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
}

#[derive(Debug, PosMacro)]
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
    pub fn new(kind: TokenKind, position: (u32, u32), value: &'a str) -> Self {
        Token {
            kind,
            position,
            value,
        }
    }

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
    P,
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
    IfKeyword,
    // if
    LetKeyword,
    // let
    ByeKeyword,
    // return
    FUNcKeyword,
    // function
    PprintKeyword,
    // write()
    PprintlnKeyword,
    // writeln()
    PpanicKeyword,
    // panic()
    PpinKeyword,
    // read()
    XxlppKeyword,
    // i64
    PpKeyword,
    // i32
    SppKeyword,
    // i16
    XsppKeyword,
    // i8
    PKeyword,
    // char
    BoobaKeyword,
    // bool
    NoppKeyword,
    // void
    YarnKeyword,
    // String
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
            Self::Number => "integer",
            Self::P => "p",
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

#[derive(Clone, Debug, Default)]
pub struct Scope<'a> {
    /// The current position in the stack frame. This is used to calculate the absolute position
    /// of the variable in the stack frame.
    current_position: u32,
    /// Variable symbol table.
    variables: std::collections::HashMap<&'a str, std::rc::Rc<Variable<'a>>>,
    /// Function symbol table.
    functions: std::collections::HashMap<&'a str, std::rc::Rc<Function<'a>>>,
}

impl<'a> Scope<'a> {
    fn push_variable(&mut self, mut variable: Variable<'a>) {
        variable.set_position_in_scope(self.current_position);
        self.current_position += variable.size_in_instructions() as u32;
        self.variables
            .insert(variable.identifier(), std::rc::Rc::new(variable));
    }

    pub fn get_variable(&self, identifier: &str) -> Option<&std::rc::Rc<Variable<'a>>> {
        self.variables.get(identifier)
    }

    pub fn remove_variable(&mut self, identifier: &str) {
        self.variables.remove(identifier);
    }

    pub fn get_variables(&self) -> std::collections::hash_map::Values<'_, &'a str, std::rc::Rc<Variable<'a>>> {
        self.variables.values()
    }

    pub fn has_variable(&self, identifier: &str) -> bool {
        self.variables.contains_key(identifier)
    }

    fn push_function(&mut self, mut function: Function<'a>) {
        self.functions
            .insert(function.identifier(), std::rc::Rc::new(function));
    }


    pub fn get_function(&self, identifier: &str) -> Option<&std::rc::Rc<Function<'a>>> {
        self.functions.get(identifier)
    }

    pub fn remove_function(&mut self, identifier: &str) {
        self.functions.remove(identifier);
    }

    pub fn get_functions(&self) -> std::collections::hash_map::Values<'_, &'a str, std::rc::Rc<Function<'a>>> {
        self.functions.values()
    }

    pub fn has_function(&self, identifier: &str) -> bool {
        self.functions.contains_key(identifier)
    }
}

#[derive(Clone, Debug)]
pub struct FunctionScope<'a> {
    scopes: Vec<Scope<'a>>,
    function_identifier: &'a str,
}

impl<'a> FunctionScope<'a> {
    pub const ACTIVATION_RECORD_SIZE: u32 = 3;

    pub fn new(function_identifier: &'a str) -> Self {
        let mut scopes = Vec::new();
        let mut scope = Scope::default();

        // Set the stack pointer AFTER the activation record.
        scope.current_position = Self::ACTIVATION_RECORD_SIZE;

        scopes.push(scope);
        FunctionScope {
            scopes,
            function_identifier,
        }
    }

    pub fn find_variable(&self, identifier: &str) -> Option<&std::rc::Rc<Variable<'a>>> {
        self.scopes
            .iter()
            .find_map(|scope| scope.get_variable(identifier))
    }

    pub fn function_identifier(&self) -> &'a str {
        self.function_identifier
    }

    pub fn push_variable(&mut self, variable: Variable<'a>) {
        self.scopes
            .last_mut()
            .expect("A scope")
            .push_variable(variable);
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    pub fn current_scope(&self) -> Option<&Scope<'a>> {
        self.scopes.last()
    }

    pub fn current_scope_mut(&mut self) -> Option<&mut Scope<'a>> {
        self.scopes.last_mut()
    }

    pub fn pop_scope(&mut self) {
        self.scopes.pop();
    }
}

#[derive(Clone, Debug)]
pub struct GlobalScope<'a> {
    scope: Scope<'a>,
}

impl<'a> GlobalScope<'a> {
    pub fn new() -> Self {
        let mut scope = Scope::default();
        // TODO: Need to offset this because we need the first
        // thing on the stack to be "1" because we call
        // main and then it fucking has to read the first thing
        // on the stack.
        scope.current_position = 1;
        GlobalScope {
            scope,
        }
    }
    fn push_variable(&mut self, variable: Variable<'a>) {
        self.scope.push_variable(variable);
    }

    pub fn has_variable(&self, identifier: &str) -> bool {
        self.scope.has_variable(identifier)
    }

    pub fn get_variable(&self, identifier: &str) -> Option<&std::rc::Rc<Variable<'a>>> {
        self.scope.get_variable(identifier)
    }

    pub fn scope(&self) -> &Scope<'a> {
        &self.scope
    }

    fn push_function(&mut self, function: Function<'a>) {
        self.scope.push_function(function);
    }

    pub fn get_function(&self, identifier: &str) -> Option<&std::rc::Rc<Function<'a>>> {
        self.scope.get_function(identifier)
    }

    pub fn has_function(&self, identifier: &str) -> bool {
        self.scope.has_function(identifier)
    }
}

pub struct SemanticAnalyzer<'a, 'b>
{
    /// The global scope holding global variables and function identifiers.
    global_scope: std::rc::Rc<std::cell::RefCell<GlobalScope<'a>>>,
    /// Current stack of function scopes.
    function_scopes: std::rc::Rc<std::cell::RefCell<Vec<FunctionScope<'a>>>>,
    /// The error diagnosis.
    error_diag: std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
}
