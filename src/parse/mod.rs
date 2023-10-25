use crate::parse::analysis::SymbolTable;
use crate::parse::emitter::Instruction;
use crate::parse::error_diagnosis::ErrorDiagnosis;
use crate::parse::parser::{Block, Expression, Function, Variable};

pub mod analysis_impl;
pub mod emitter_impl;
pub mod error_diagnosis;
pub mod lexer_impl;
pub mod parser_impl;

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

mod lexer {
    use dpp_macros::PosMacro;
    use dpp_macros_derive::PosMacro;

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

    impl std::fmt::Display for Token<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{} ({})", self.value, self.kind)
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

    impl std::fmt::Display for TokenKind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
}

mod parser {
    use dpp_macros::PosMacro;
    use dpp_macros_derive::PosMacro;

    use crate::parse::{BinaryOperator, Number, Statement, UnaryOperator};

    #[derive(Clone, Debug, PosMacro)]
    pub struct TranslationUnit<'a> {
        position: (u32, u32),
        functions: Vec<Function<'a>>,
        global_statements: Vec<Statement<'a>>,
    }

    impl<'a> TranslationUnit<'a> {
        pub fn new(functions: Vec<Function<'a>>, global_statements: Vec<Statement<'a>>) -> Self {
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
        position_in_function_scope: Option<usize>,
        identifier: &'a str,
        data_type: DataType<'a>,
        size: usize,
        value: Option<Expression<'a>>,
        is_parameter: bool,
    }

    impl<'a> Variable<'a> {
        pub fn new(
            position: (u32, u32),
            identifier: &'a str,
            data_type: DataType<'a>,
            value: Option<Expression<'a>>,
            is_parameter: bool,
        ) -> Self {
            Variable {
                position,
                position_in_function_scope: None,
                identifier,
                size: data_type.size(),
                data_type,
                value,
                is_parameter,
            }
        }

        pub fn is_initialized(&self) -> bool {
            self.is_parameter || self.value.is_some()
        }

        pub fn position(&self) -> (u32, u32) {
            self.position
        }
        pub fn position_in_scope(&self) -> Option<usize> {
            self.position_in_function_scope
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

        pub fn set_position_in_scope(&mut self, position_in_scope: usize) {
            self.position_in_function_scope = Some(position_in_scope);
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
        Invalid,
    }

    impl PosMacro for Expression<'_> {
        // TODO: Implement the macro for this later.
        fn row(&self) -> u32 {
            match self {
                Expression::Number { position, .. } => position.0,
                Expression::P { position, .. } => position.0,
                Expression::Booba { position, .. } => position.0,
                Expression::Yarn { position, .. } => position.0,
                Expression::Unary { position, .. } => position.0,
                Expression::Binary { position, .. } => position.0,
                Expression::Identifier { position, .. } => position.0,
                Expression::FunctionCall { position, .. } => position.0,
                Expression::Invalid => 0,
            }
        }

        fn col(&self) -> u32 {
            match self {
                Expression::Number { position, .. } => position.1,
                Expression::P { position, .. } => position.1,
                Expression::Booba { position, .. } => position.1,
                Expression::Yarn { position, .. } => position.1,
                Expression::Unary { position, .. } => position.1,
                Expression::Binary { position, .. } => position.1,
                Expression::Identifier { position, .. } => position.1,
                Expression::FunctionCall { position, .. } => position.1,
                Expression::Invalid => 0,
            }
        }
    }

    impl std::fmt::Display for Expression<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

    impl std::fmt::Display for DataType<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
                DataType::Nopp => 0,
                _ => panic!("Invalid data type {self}"),
            }
        }

        pub fn size_in_instructions(&self) -> usize {
            let size = self.size();
            if size == 0 {
                return 0;
            }
            return ((size - 1) / 4) + 1;
        }
    }
}

mod analysis {
    use std::collections::HashMap;

    use crate::parse::parser::{Function, Variable};

    #[derive(Clone, Debug)]
    pub struct SymbolTable<'a> {
        /// The global scope holding global variables and function identifiers.
        global_scope: GlobalScope<'a>,
        /// Current stack of function scopes.
        function_scopes: Vec<FunctionScope<'a>>,
    }

    impl<'a> SymbolTable<'a> {
        pub fn new() -> Self {
            SymbolTable {
                global_scope: GlobalScope::new(),
                function_scopes: Vec::new(),
            }
        }

        pub fn get_variable_level_and_offset(
            &self,
            identifier: &str,
            function_ident: Option<&'a str>,
        ) -> (u32, usize) {
            if let Some(function_ident) = function_ident {
                if let Some(function_scope) = self.function_scope(function_ident) {
                    if let Some(variable) = function_scope.find_variable(identifier) {
                        return (
                            0,
                            variable
                                .position_in_scope()
                                .expect("Initialized variable position"),
                        );
                    }
                }
            }

            use std::borrow::Borrow;
            // If not found, try to find it in the global scope.
            (
                1,
                self.global_scope
                    .borrow()
                    .get_variable(identifier)
                    .unwrap_or_else(|| panic!("Unknown variable {identifier}"))
                    .position_in_scope()
                    .expect("Initialized variable position"),
            )
        }

        pub fn push_global_variable(&mut self, variable: Variable<'a>) {
            self.global_scope.push_variable(variable);
        }

        pub fn push_local_variable(&mut self, variable: Variable<'a>) {
            self.current_function_scope_mut().push_variable(variable);
        }

        pub fn push_global_function(&mut self, function: Function<'a>) {
            self.global_scope.push_function(function);
        }

        fn new_function_scope(&mut self, function_identifier: &'a str) {
            self.function_scopes
                .push(FunctionScope::new(function_identifier))
        }

        pub fn find_function(&self, identifier: &str) -> Option<&std::rc::Rc<Function<'a>>> {
            self.global_scope.get_function(identifier)
        }

        pub fn push_scope(&mut self) {
            self.current_function_scope_mut().push_scope();
        }

        pub fn pop_scope(&mut self) {
            self.current_function_scope_mut().pop_scope();
        }

        pub fn find_variable(
            &self,
            identifier: &str,
            function_ident: Option<&'a str>,
        ) -> Option<&std::rc::Rc<Variable<'a>>> {
            self.find_local_variable(identifier, function_ident)
                .or_else(|| self.find_global_variable(identifier))
        }

        pub fn push_function(&mut self, function: Function<'a>) {
            self.new_function_scope(function.identifier());
            self.global_scope.push_function(function);
        }

        pub fn find_global_variable(&self, identifier: &str) -> Option<&std::rc::Rc<Variable<'a>>> {
            self.global_scope.get_variable(identifier)
        }

        pub fn find_local_variable(
            &self,
            identifier: &str,
            function_ident: Option<&'a str>,
        ) -> Option<&std::rc::Rc<Variable<'a>>> {
            self.function_scope(function_ident?)?
                .find_variable(identifier)
        }

        pub fn get_variables(&self) -> HashMap<&str, &std::rc::Rc<Variable<'a>>> {
            let mut variables = HashMap::new();
            if let Some(function_scope) = self.function_scopes.last() {
                for scope in function_scope.scopes() {
                    for (k, v) in scope.variables() {
                        variables.insert(*k, v);
                    }
                }
            }
            variables
        }

        // TODO: This could be done in O(1) but w/e.
        pub fn function_scope(&self, function_identifier: &str) -> Option<&FunctionScope<'a>> {
            self.function_scopes
                .iter()
                .find(move |func| func.function_identifier == function_identifier)
        }

        pub fn current_function_scope(&self) -> &FunctionScope<'a> {
            self.function_scopes.last().expect("Inside function scope")
        }

        pub fn current_function_scope_mut(&mut self) -> &mut FunctionScope<'a> {
            self.function_scopes
                .last_mut()
                .expect("Inside function scope")
        }
    }

    #[derive(Clone, Debug)]
    pub struct Scope<'a> {
        /// The current position in the stack frame. This is used to calculate the absolute position
        /// of the variable in the stack frame.
        current_position: usize,
        /// Variable symbol table.
        variables: std::collections::HashMap<&'a str, std::rc::Rc<Variable<'a>>>,
        /// Function symbol table.
        functions: std::collections::HashMap<&'a str, std::rc::Rc<Function<'a>>>,
        parent: Option<Scope<'a>>,
        children: Vec<Scope<'a>>,
    }

    impl<'a> Scope<'a> {
        pub fn new(start_position: usize) -> Self {
            Scope {
                current_position: start_position,
                variables: HashMap::new(),
                functions: HashMap::new(),
                parent: None,
                children: Vec::new(),
            }
        }
        fn push_variable(&mut self, mut variable: Variable<'a>) {
            variable.set_position_in_scope(self.current_position);
            self.current_position += variable.size_in_instructions();
            self.variables
                .insert(variable.identifier(), std::rc::Rc::new(variable));
        }

        pub fn get_variable(&self, identifier: &str) -> Option<&std::rc::Rc<Variable<'a>>> {
            self.variables.get(identifier)
        }

        pub fn remove_variable(&mut self, identifier: &str) {
            self.variables.remove(identifier);
        }

        pub fn get_variables(
            &self,
        ) -> std::collections::hash_map::Values<'_, &'a str, std::rc::Rc<Variable<'a>>> {
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

        pub fn get_functions(
            &self,
        ) -> std::collections::hash_map::Values<'_, &'a str, std::rc::Rc<Function<'a>>> {
            self.functions.values()
        }

        pub fn has_function(&self, identifier: &str) -> bool {
            self.functions.contains_key(identifier)
        }
        pub fn current_position(&self) -> usize {
            self.current_position
        }
        pub fn variables(&self) -> &std::collections::HashMap<&'a str, std::rc::Rc<Variable<'a>>> {
            &self.variables
        }
        pub fn functions(&self) -> &std::collections::HashMap<&'a str, std::rc::Rc<Function<'a>>> {
            &self.functions
        }
    }

    #[derive(Clone, Debug)]
    pub struct FunctionScope<'a> {
        scopes: Vec<Scope<'a>>,
        function_identifier: &'a str,
    }

    impl<'a> FunctionScope<'a> {
        pub const ACTIVATION_RECORD_SIZE: usize = 3;

        pub fn new(function_identifier: &'a str) -> Self {
            FunctionScope {
                scopes: Vec::new(),
                function_identifier,
            }
        }

        pub fn find_variable(&self, identifier: &str) -> Option<&std::rc::Rc<Variable<'a>>> {
            self.scopes
                .iter()
                .rev()
                .find_map(|scope| scope.get_variable(identifier))
        }

        pub fn variable_count(&self) -> usize {
            self.scopes
                .iter()
                .fold(0, |accum, scope| accum + scope.variables.len())
        }

        pub fn function_identifier(&self) -> &'a str {
            self.function_identifier
        }

        pub fn push_variable(&mut self, variable: Variable<'a>) {
            self.current_scope_mut()
                .expect("A scope")
                .push_variable(variable);
        }

        pub fn push_scope(&mut self) {
            if let Some(previous_scope) = self.scopes.last() {
                self.scopes
                    .push(Scope::new(previous_scope.current_position + 1));
            } else {
                self.scopes.push(Scope::new(Self::ACTIVATION_RECORD_SIZE));
            }
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

        pub fn scopes(&self) -> &Vec<Scope<'a>> {
            &self.scopes
        }
    }

    #[derive(Clone, Debug)]
    pub struct GlobalScope<'a> {
        scope: Scope<'a>,
    }

    impl<'a> GlobalScope<'a> {
        pub fn new() -> Self {
            // TODO: Need to offset this because we need the first
            // thing on the stack to be "1" because we call
            // main and then it fucking has to read the first thing
            // on the stack.
            GlobalScope {
                scope: Scope::new(1),
            }
        }
        pub fn push_variable(&mut self, variable: Variable<'a>) {
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

        pub fn push_function(&mut self, function: Function<'a>) {
            self.scope.push_function(function);
        }

        pub fn get_function(&self, identifier: &str) -> Option<&std::rc::Rc<Function<'a>>> {
            self.scope.get_function(identifier)
        }

        pub fn has_function(&self, identifier: &str) -> bool {
            self.scope.has_function(identifier)
        }
    }
}

pub struct SemanticAnalyzer<'a, 'b> {
    symbol_table: SymbolTable<'a>,
    error_diag: std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
    current_function: Option<&'a str>,
    loop_stack: usize,
    scope_index: usize,
}

impl<'a, 'b> SemanticAnalyzer<'a, 'b> {
    pub fn new(error_diag: std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, 'b>>>) -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            error_diag,
            current_function: None,
            loop_stack: 0,
            scope_index: 0,
        }
    }

    pub fn symbol_table_mut(&mut self) -> &mut SymbolTable<'a> {
        &mut self.symbol_table
    }

    pub fn symbol_table(&self) -> &SymbolTable<'a> {
        &self.symbol_table
    }
}

#[derive(Clone, Debug)]
pub enum Statement<'a> {
    VariableDeclaration {
        variable: Variable<'a>,
    },
    If {
        position: (u32, u32),
        expression: Expression<'a>,
        statement: Box<Statement<'a>>,
    },
    IfElse {
        position: (u32, u32),
        expression: Expression<'a>,
        statement: Box<Statement<'a>>,
        else_statement: Box<Statement<'a>>,
    },
    Bye {
        position: (u32, u32),
        expression: Option<Expression<'a>>,
    },
    Print {
        position: (u32, u32),
        print_function: fn(&str),
        expression: Expression<'a>,
    },
    Block {
        position: (u32, u32),
        block: Box<Block<'a>>,
    },
    Expression {
        position: (u32, u32),
        expression: Expression<'a>,
    },
    Empty {
        position: (u32, u32),
    },
    For {
        position: (u32, u32),
        index_ident: &'a str,
        ident_expression: Option<Expression<'a>>,
        length_expression: Expression<'a>,
        statement: Box<Statement<'a>>,
    },
    While {
        position: (u32, u32),
        expression: Expression<'a>,
        statement: Box<Statement<'a>>,
    },
    DoWhile {
        position: (u32, u32),
        block: Block<'a>,
        expression: Expression<'a>,
    },
    Loop {
        position: (u32, u32),
        block: Box<Block<'a>>,
    },
    Break {
        position: (u32, u32),
    },
    Continue {
        position: (u32, u32),
    },
    Switch {
        position: (u32, u32),
        expression: Expression<'a>,
        cases: Vec<Case<'a>>,
    },
    Assignment {
        position: (u32, u32),
        identifier: &'a str,
        expression: Expression<'a>,
    },
}

#[derive(Clone, Debug)]
pub struct Case<'a> {
    expression: Expression<'a>,
    block: Box<Block<'a>>,
}

impl<'a> Case<'a> {
    pub fn expression(&self) -> &Expression<'a> {
        &self.expression
    }
    pub fn block(&self) -> &Box<Block<'a>> {
        &self.block
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Number {
    Pp,
    Spp,
    Xspp,
}

#[derive(Clone, Debug)]
pub struct Struct {}

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
pub enum UnaryOperator {
    Not,
    Negate,
}

mod emitter {
    #[derive(Clone, Debug)]
    pub enum Address {
        Absolute(u32),
        Label(String),
    }

    impl std::fmt::Display for Address {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Absolute(absolute_address) => write!(f, "{absolute_address}")?,
                Self::Label(label) => write!(f, "@{label}")?,
            };

            Ok(())
        }
    }

    #[derive(Clone, Debug)]
    pub(crate) enum Instruction {
        /// Push the literal value arg onto the stack.
        Literal {
            value: i32,
        },
        /// Return from a subroutine. This instruction uses the stack frame (or block mark) from the current invocation of the subroutine to clear the stack of all data local to the current subroutine, restore the base register, and restore the program counter. Like all operations which require no arguments, it uses the op code OPR, with a second argument (here zero) indicating which of the zero-argument operations to perform.
        Operation {
            operation: Operation,
        },
        /// Load (i.e. push onto the stack) the value of the cell identified by level and offset. A level value of 0 means the variable is in the currently executing procedure; 1 means it's in the immediately enclosing region of the program. 2 means it's the region outside that (in PL/0 as in Pascal procedures can nest indefinitely). The offset distinguishes among the variables declared at that level.
        Load {
            level: u32,
            offset: i32,
        },
        /// Store the value currently at the top of the stack to the memory cell identified by level and offset, popping the value off the stack in the process.
        Store {
            level: u32,
            offset: i32,
        },
        /// Call the subroutine at location address, which is level nesting levels different from the nesting level of the currently executing code. This instruction pushes a stack frame (or block mark) onto the stack, storing
        ///
        ///     the base address for variables, level blocks down on the stack (so that variables in outer blocks can be referred to and modified)
        ///     the current base address (so that it can be restored when the subroutine returns)
        ///     the current program counter (so that it can be restored when the subroutine returns)
        Call {
            level: u32,
            address: Address,
        },
        Return,
        Int {
            size: i32,
        },
        /// Jump to the instruction at address.
        Jump {
            address: Address,
        },
        /// Pop the current value from the top of the stack. If it's 0 (false), jump to the instruction at address. Otherwise, continue with the current location of the program counter.
        Jmc {
            address: Address,
        },
        // TODO: Those aren't instructions! Make a new enum.
        Dbg {
            debug_keyword: DebugKeyword,
        },
        Label(String),
    }

    impl std::fmt::Display for Instruction {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{self:?}")
            // or, alternatively:
            // fmt::Debug::fmt(self, f)
        }
    }

    #[derive(Clone, Copy, Debug)]
    pub enum Operation {
        Return = 0,
        /// Negate the value on the top of the stack (i.e. multiply by -1).
        Negate = 1,
        /// Add the two values at the top of the stack and replace them with their sum.
        Add = 2,
        /// Subtract the value at the top of the stack from the value below it; replace the diminuend and the subtrahend with their difference.
        Subtract = 3,
        /// Multiply the two values at the top of the stack and replace them with their product.
        Multiply = 4,
        /// Perform integer division on the two values at the top of the stack. The value on top of the stack becomes the divisor, the value below it the dividend. Replace the two values with their integer quotient.
        Divide = 5,
        Mod = 6,
        /// Test the value at the top of the stack to see if it's odd or not.
        Odd = 7,
        /// Test the two values at the top of the stack to see if they are equal or not.
        Equal = 8,
        /// Test the two values at the top of the stack to see if they are unequal or not.
        NotEqual = 9,
        /// Test the two values x and y at the top of the stack to see if x is less than y or not.
        LessThan = 10,
        /// Test the two values x and y at the top of the stack to see if x is greater than y or not.
        GreaterThanOrEqualTo = 11,
        /// Test the two values x and y at the top of the stack to see if x is greater than or equal to y, or not.
        GreaterThan = 12,
        /// Test the two values x and y at the top of the stack to see if x is less than or equal to y, or not.
        LessThanOrEqualTo = 13,
    }

    #[derive(Clone, Debug)]
    pub enum DebugKeyword {
        Registers,
        Stack,
        StackA,
        StackRg { start: u32, end: u32 },
        StackN { amount: u32 },
        Echo { message: String },
    }

    pub(crate) const EMIT_DEBUG: bool = true;
}

pub struct Emitter<'a> {
    /// The instructions to be emitted.
    code: Vec<Instruction>,
    /// Stack of function scopes. Each scope is pushed and popped when entering and exiting a function.
    symbol_table: std::rc::Rc<SymbolTable<'a>>,
    /// The labels of the program.
    labels: std::collections::HashMap<String, u32>,
    current_function: Option<&'a str>,
    function_scope_depth: std::collections::HashMap<&'a str, u32>,
    control_statement_count: u32,
}

pub mod compiler {
    use std::cell::RefCell;
    use std::error::Error;
    use std::fs;
    use std::rc::Rc;

    use crate::parse::analysis::SymbolTable;
    use crate::parse::error_diagnosis::ErrorDiagnosis;
    use crate::parse::lexer::Token;
    use crate::parse::parser::TranslationUnit;
    use crate::parse::parser_impl::Parser;
    use crate::parse::{Emitter, Lexer, SemanticAnalyzer};

    pub struct DppCompiler;

    const DEBUG: bool = false;

    impl DppCompiler {
        pub fn compile_translation_unit(
            file_path: &str,
            output_file: &str,
            pl0_interpret_path: &str,
        ) -> Result<(), Box<dyn Error>> {
            let file_contents = fs::read_to_string(file_path)?;
            let error_diag = std::rc::Rc::new(std::cell::RefCell::new(ErrorDiagnosis::new(
                file_path,
                &file_contents,
            )));
            // Lex -> parse -> analyze -> emit.
            // Pass error diag to each step.
            println!("Parsing program...");
            let start = std::time::Instant::now();
            let tokens = Self::lex(&file_contents, &error_diag)?;
            dbg!(&tokens);
            let translation_unit = Self::parse(tokens, &error_diag)?;
            dbg!(&translation_unit);
            let symbol_table = Self::analyze(&error_diag, &translation_unit)?;
            let duration = start.elapsed();
            println!("Program parsed in {:?}", duration);

            // Create a Rc<T> because the emitter is NOT allowed to modify the symbol table.
            // The emitter is only allowed to look up functions, variables etc.
            println!("Emitting program...");
            let start = std::time::Instant::now();
            Self::emit(output_file, &translation_unit, symbol_table)?;
            let duration = start.elapsed();
            println!("Program emitted in {:?}", duration);
            let child = std::process::Command::new(pl0_interpret_path)
                .args(["-a", "+d", "+l", "+i", "+t", "+s", output_file])
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()?;

            let out = child.wait_with_output()?;
            let stdout = String::from_utf8(out.stdout)?;
            let stderr = String::from_utf8(out.stderr)?;

            if DEBUG {
                println!("{stdout}");
            }

            if !stderr.is_empty() {
                eprintln!("ERROR: {stderr}");
            }
            Ok(())
        }

        fn emit(
            output_file: &str,
            translation_unit: &TranslationUnit,
            symbol_table: SymbolTable,
        ) -> Result<(), Box<dyn Error>> {
            let mut emitter = Emitter::new(std::rc::Rc::new(symbol_table));

            let file = fs::File::create(output_file)?;
            let mut writer = std::io::BufWriter::new(file);
            emitter.emit_all(&mut writer, &translation_unit)?;
            Ok(())
        }

        fn analyze<'a>(
            error_diag: &Rc<RefCell<ErrorDiagnosis<'a, '_>>>,
            translation_unit: &TranslationUnit<'a>,
        ) -> Result<SymbolTable<'a>, Box<dyn Error>> {
            let mut analyzer = SemanticAnalyzer::new(std::rc::Rc::clone(&error_diag));
            analyzer.analyze(&translation_unit);
            error_diag.borrow().check_errors()?;
            Ok(analyzer.into_symbol_table())
        }

        fn lex<'a>(
            input: &'a str,
            error_diag: &std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, '_>>>,
        ) -> Result<Vec<Token<'a>>, Box<dyn Error>> {
            let mut lexer = Lexer::new(input, error_diag.clone());
            let tokens = lexer.lex();
            error_diag.borrow().check_errors()?;
            Ok(tokens)
        }

        fn parse<'a>(
            tokens: Vec<Token<'a>>,
            error_diag: &std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, '_>>>,
        ) -> Result<TranslationUnit<'a>, Box<dyn Error>> {
            let mut parser = Parser::new(std::rc::Rc::new(tokens), error_diag.clone());
            let result = parser.parse();
            error_diag.borrow().check_errors()?;
            Ok(result)
        }
    }

    #[cfg(test)]
    mod tests {
        #[test]
        fn test() {
            assert_eq!(1, 1);
        }
    }
}
