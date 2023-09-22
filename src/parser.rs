use crate::error_diagnosis::ErrorDiagnosis;
use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;

use crate::lexer::{Token, TokenKind};
use crate::parser::Statement::EmptyStatement;

#[derive(Debug)]
pub struct Parser {
    tokens: Rc<Vec<Token>>,
    error_diag: Rc<RefCell<ErrorDiagnosis>>,
    curr_token_index: usize,
}

#[derive(Debug)]
pub enum Statement {
    VariableDeclaration {
        identifier: String,
        data_type: DataType,
    },
    VariableDeclarationAndAssignment {
        identifier: String,
        data_type: DataType,
        expression: Expression,
    },
    IfStatement {
        expression: Expression,
        statement: Box<Statement>,
    },
    IfElseStatement {
        expression: Expression,
        statement: Box<Statement>,
        else_statement: Box<Statement>,
    },
    ReturnStatement {
        expression: Expression,
    },
    BlockStatement {
        block: Box<Block>,
    },
    ExpressionStatement {
        expression: Expression,
    },
    EmptyStatement,
}

impl Default for Statement {
    fn default() -> Self {
        EmptyStatement
    }
}

#[derive(Debug)]
pub struct TranslationUnit {
    pub functions: Vec<Function>,
    pub variables: Vec<Statement>,
}

#[derive(Debug)]
pub struct Function {
    pub identifier: String,
    pub return_type: DataType,
    pub parameters: Vec<Parameter>,
    pub block: Block,
}

#[derive(Debug)]
pub struct Parameters {
    pub parameters: Vec<Parameter>,
}

#[derive(Debug)]
pub struct Parameter {
    pub identifier: String,
    pub data_type: DataType,
}

#[derive(Debug)]
pub struct Variable {
    pub identifier: String,
    pub data_type: DataType,
}

#[derive(Debug, Default)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub enum Expression {
    PpExpression(i32),
    BoobaExpression(bool),
    FiberExpression(String),
    UnaryExpression {
        op: UnaryOperator,
        operand: Box<Expression>,
    },
    BinaryExpression {
        lhs: Box<Expression>,
        op: BinaryOperator,
        rhs: Box<Expression>,
    },
    IdentifierExpression {
        identifier: String,
    },
    FunctionCall {
        arguments: Vec<Expression>,
    },
    AssignmentExpression {
        expression: Box<Expression>,
    },
    EmptyExpression,
}

impl Default for Expression {
    fn default() -> Self {
        Self::EmptyExpression
    }
}

#[derive(Debug)]
pub enum DataType {
    Pp,
    Struct(Struct),
    EmptyDataType,
}

impl Default for DataType {
    fn default() -> Self {
        Self::EmptyDataType
    }
}

#[derive(Debug)]
pub enum Struct {
    EmptyStruct,
}

impl Default for Struct {
    fn default() -> Self {
        Self::EmptyStruct
    }
}

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
    EmptyOperator,
}

impl Default for BinaryOperator {
    fn default() -> Self {
        Self::EmptyOperator
    }
}

#[derive(Debug)]
pub enum UnaryOperator {
    Not,
    Negate,
    EmptyOperator,
}

impl Default for UnaryOperator {
    fn default() -> Self {
        Self::EmptyOperator
    }
}

impl Parser {
    pub fn new(tokens: Rc<Vec<Token>>, error_diag: Rc<RefCell<ErrorDiagnosis>>) -> Self {
        Self {
            tokens,
            curr_token_index: 0,
            error_diag,
        }
    }

    fn consume_token(&mut self) {
        self.curr_token_index += 1;
    }

    #[must_use]
    fn token(&self) -> Option<&Token> {
        return self.token_offset(0);
    }

    #[must_use]
    fn token_offset(&self, offset: i32) -> Option<&Token> {
        if self.curr_token_index as i32 + offset >= self.tokens.len() as i32
            || self.curr_token_index as i32 + offset < 0
        {
            return None;
        }
        Some(&self.tokens[(self.curr_token_index as i32 + offset) as usize])
    }
    pub fn parse(&mut self) -> TranslationUnit {
        self.translation_unit()
    }

    fn translation_unit(&mut self) -> TranslationUnit {
        let mut functions = Vec::<Function>::new();
        let mut variables = Vec::<Statement>::new();
        loop {
            if let Some(function) = self.function() {
                functions.push(function);
            } else if let Some(variable_declaration) = self.variable_declaration() {
                variables.push(variable_declaration);
            } else if self.curr_token_index == self.tokens.len() {
                break;
            } else if let Some(token) = self.token() {
                self.error_diag.borrow_mut().invalid_token_error(token);
                self.consume_token();
            } else {
                panic!("Something unexpected happened :( (compiler error)")
            }
        }
        TranslationUnit {
            functions,
            variables,
        }
    }

    fn function(&mut self) -> Option<Function> {
        self.match_token_maybe(TokenKind::FUNcKeyword)?;

        let identifier = self.match_token(TokenKind::Identifier);
        self.match_token(TokenKind::OpenParen);
        let parameters = self.parameters();
        self.match_token(TokenKind::CloseParen);
        self.match_token(TokenKind::Colon);
        let return_type = self.match_something(Self::data_type, "data type");
        let block = self.match_something(Self::block, "block");

        Some(Function {
            identifier,
            return_type,
            parameters,
            block,
        })
    }

    fn variable_declaration(&mut self) -> Option<Statement> {
        self.match_token_maybe(TokenKind::LetKeyword)?;

        let identifier = self.match_token(TokenKind::Identifier);
        self.match_token(TokenKind::Colon);
        let data_type = self.data_type()?;
        let statement = if self.match_token_maybe(TokenKind::Equal).is_some() {
            let expression = self.match_something(Self::expression, "expression");
            Statement::VariableDeclarationAndAssignment {
                identifier,
                data_type,
                expression,
            }
        } else {
            Statement::VariableDeclaration {
                identifier,
                data_type,
            }
        };

        self.match_token(TokenKind::Semicolon);
        Some(statement)
    }

    fn binop(&mut self, op_matcher: fn(&TokenKind) -> BinaryOperator) -> BinaryOperator {
        let operator = self.token().expect("Failed to get token");
        let kind = &operator.kind();
        let op = op_matcher(kind);
        self.consume_token();
        op
    }

    fn unop(&mut self, op_matcher: fn(&TokenKind) -> UnaryOperator) -> UnaryOperator {
        let operator = self.token().expect("Failed to get token");
        let kind = &operator.kind();
        let op = op_matcher(kind);
        self.consume_token();
        op
    }

    fn parameters(&mut self) -> Vec<Parameter> {
        let mut parameters = Vec::<Parameter>::new();
        while let Some(parameter) = self.parameter() {
            parameters.push(parameter);
            if self.match_token_maybe(TokenKind::Comma).is_none() {
                break;
            }
        }
        parameters
    }

    fn parameter(&mut self) -> Option<Parameter> {
        let identifier = self.match_token_maybe(TokenKind::Identifier)?;
        self.match_token(TokenKind::Colon);
        let data_type = self.match_something(Self::data_type, "data type");
        Some(Parameter {
            identifier,
            data_type,
        })
    }

    fn block(&mut self) -> Option<Block> {
        self.match_token_maybe(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement>::new();
        while let Some(statement) = self.statement() {
            statements.push(statement);
        }
        self.match_token(TokenKind::CloseBrace);

        Some(Block { statements })
    }

    fn statement(&mut self) -> Option<Statement> {
        if let Some(variable_declaration) = self.variable_declaration() {
            return Some(variable_declaration);
        } else if self.match_token_maybe(TokenKind::IfKeyword).is_some() {
            self.match_token(TokenKind::OpenParen);
            let expression = self.match_something(Self::expression, "expression");
            self.match_token(TokenKind::CloseParen);

            let statement = self.match_something(Self::statement, "statement");
            return if self.match_token_maybe(TokenKind::ElseKeyword).is_some() {
                let else_statement = self.match_something(Self::statement, "statement");
                Some(Statement::IfElseStatement {
                    expression,
                    statement: Box::new(statement),
                    else_statement: Box::new(else_statement),
                })
            } else {
                Some(Statement::IfStatement {
                    expression,
                    statement: Box::new(statement),
                })
            };
        } else if let Some(block) = self.block() {
            return Some(Statement::BlockStatement {
                block: Box::new(block),
            });
        } else if self.match_token_maybe(TokenKind::ByeKeyword).is_some() {
            let expression = self.match_something(Self::expression, "expression");
            self.match_token(TokenKind::Semicolon);

            return Some(Statement::ReturnStatement { expression });
        } else if let Some(expression) = self.expression() {
            self.match_token(TokenKind::Semicolon);

            return Some(Statement::ExpressionStatement { expression });
        } else if self.match_token_maybe(TokenKind::Semicolon).is_some() {
            return Some(EmptyStatement);
        }

        None
    }

    fn data_type(&mut self) -> Option<DataType> {
        if let Some(token) = self.token() {
            return match token.kind() {
                TokenKind::PpType => {
                    self.consume_token();
                    Some(DataType::Pp)
                }
                _ => None,
            };
        }
        None
    }

    fn _struct_(&mut self) -> Option<DataType> {
        todo!()
    }

    fn expression(&mut self) -> Option<Expression> {
        self.equality()
    }

    fn equality(&mut self) -> Option<Expression> {
        let mut comparison = self.comparison();

        while self.matches_token_kind(TokenKind::BangEqual)
            || self.matches_token_kind(TokenKind::EqualEqual)
        {
            if let Some(expression) = comparison {
                let op = self.binop(|kind| match kind {
                    TokenKind::BangEqual => BinaryOperator::NotEqual,
                    TokenKind::EqualEqual => BinaryOperator::Equal,
                    _ => unreachable!(),
                });
                let rhs = self.match_something(Self::comparison, "expression");
                comparison = Some(Expression::BinaryExpression {
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }
        comparison
    }

    fn comparison(&mut self) -> Option<Expression> {
        let mut term = self.term();

        while self.matches_token_kind(TokenKind::Greater)
            || self.matches_token_kind(TokenKind::GreaterEqual)
            || self.matches_token_kind(TokenKind::Less)
            || self.matches_token_kind(TokenKind::LessEqual)
        {
            if let Some(expression) = term {
                let op = self.binop(|kind| match kind {
                    TokenKind::Greater => BinaryOperator::GreaterThan,
                    TokenKind::GreaterEqual => BinaryOperator::GreaterThanOrEqual,
                    TokenKind::Less => BinaryOperator::LessThan,
                    TokenKind::LessEqual => BinaryOperator::LessThanOrEqual,
                    _ => unreachable!(),
                });
                let rhs = self.match_something(Self::term, "expression");
                term = Some(Expression::BinaryExpression {
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }
        term
    }

    fn term(&mut self) -> Option<Expression> {
        let mut factor = self.factor();

        while self.matches_token_kind(TokenKind::Dash) || self.matches_token_kind(TokenKind::Plus) {
            if let Some(expression) = factor {
                let op = self.binop(|kind| match kind {
                    TokenKind::Dash => BinaryOperator::Subtract,
                    TokenKind::Plus => BinaryOperator::Add,
                    _ => unreachable!(),
                });
                let rhs = self.match_something(Self::factor, "expression");
                factor = Some(Expression::BinaryExpression {
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }

        factor
    }

    fn factor(&mut self) -> Option<Expression> {
        let mut expression = self.unary();

        while self.matches_token_kind(TokenKind::ForwardSlash)
            || self.matches_token_kind(TokenKind::Star)
        {
            if expression.is_some() {
                let op = self.binop(|kind| match kind {
                    TokenKind::ForwardSlash => BinaryOperator::Divide,
                    TokenKind::Star => BinaryOperator::Multiply,
                    _ => unreachable!(),
                });
                let rhs = self.match_something(Self::unary, "expression");
                expression = Some(Expression::BinaryExpression {
                    lhs: Box::new(expression.unwrap()),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }
        expression
    }

    fn unary(&mut self) -> Option<Expression> {
        if self.matches_token_kind(TokenKind::Bang) || self.matches_token_kind(TokenKind::Dash) {
            let op = self.unop(|kind| match kind {
                TokenKind::Bang => UnaryOperator::Not,
                TokenKind::Dash => UnaryOperator::Negate,
                _ => unreachable!(),
            });
            let operand = self.match_something(Self::unary, "expression");
            return Some(Expression::UnaryExpression {
                op,
                operand: Box::new(operand),
            });
        }

        self.primary()
    }

    fn primary(&mut self) -> Option<Expression> {
        if let Some(identifier) = self.match_token_maybe(TokenKind::Identifier) {
            return if self.match_token_maybe(TokenKind::OpenParen).is_some() {
                let arguments = self.arguments();
                self.match_token(TokenKind::CloseParen);

                Some(Expression::FunctionCall { arguments })
            } else if self.match_token_maybe(TokenKind::Equal).is_some() {
                let expression = self.match_something(Self::expression, "expression");
                Some(Expression::AssignmentExpression {
                    expression: Box::new(expression),
                })
            } else {
                Some(Expression::IdentifierExpression { identifier })
            };
        } else if self.match_token_maybe(TokenKind::NomKeyword).is_some() {
            return Some(Expression::BoobaExpression(false));
        } else if self.match_token_maybe(TokenKind::YemKeyword).is_some() {
            return Some(Expression::BoobaExpression(true));
        } else if let Some(number) = self.match_token_maybe(TokenKind::Number) {
            return Some(Expression::PpExpression(number.parse::<i32>().unwrap()));
        } else if let Some(fiber) = self.match_token_maybe(TokenKind::FiberType) {
            return Some(Expression::FiberExpression(fiber));
        } else if self.match_token_maybe(TokenKind::OpenParen).is_some() {
            let expression = self.match_something(Self::expression, "expression");
            self.match_token(TokenKind::CloseParen);
            return Some(expression);
        }

        None
    }

    fn arguments(&mut self) -> Vec<Expression> {
        let mut args = Vec::<Expression>::new();
        while let Some(expression) = self.expression() {
            args.push(expression);
            if self.match_token_maybe(TokenKind::Comma).is_none() {
                break;
            }
        }

        args
    }

    fn matches_token_kind(&mut self, token_kind: TokenKind) -> bool {
        if let Some(token) = self.token() {
            return token.kind() == token_kind;
        }
        false
    }

    fn match_token_maybe(&mut self, token_kind: TokenKind) -> Option<String> {
        if let Some(token) = self.token() {
            if token.kind() == token_kind {
                let optional_token_value = token.value();
                self.consume_token();
                if let Some(token_value) = optional_token_value {
                    return Some(token_value);
                }
                return Some(String::new());
            }
        }

        None
    }

    fn match_token(&mut self, token_kind: TokenKind) -> String {
        if let Some(token) = self.token() {
            if token.kind() == token_kind {
                let token_value = token.value();
                self.consume_token();
                if let Some(token_value) = token_value {
                    return token_value;
                }
            } else if let Some(prev_token) = self.token_offset(-1) {
                self.error_diag
                    .borrow_mut()
                    .expected_different_token_error(prev_token, token_kind);
            } else {
                self.error_diag.borrow_mut().handle("No token found");
            }
        }
        String::new()
    }

    fn match_something<T: Default>(
        &mut self,
        grammar_func: fn(&mut Self) -> Option<T>,
        error_message: &str,
    ) -> T {
        if let Some(ret_from_something) = grammar_func(self) {
            return ret_from_something;
        }
        self.error_diag
            .borrow_mut()
            .expected_something_error(error_message, self.token_offset(-1));
        T::default()
    }
}
