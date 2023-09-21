use std::fmt::Debug;

use crate::lexer::{Lexer, TokenKind};

#[derive(Default)]
pub struct Parser;

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

#[derive(Debug, Clone)]
pub struct Variable {
    pub identifier: String,
    pub data_type: DataType,
}

#[derive(Debug)]
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
}

#[derive(Debug, Copy, Clone)]
pub enum DataType {
    Pp,
    Struct(Struct),
}

#[derive(Debug, Copy, Clone)]
pub enum Struct {}

#[derive(Copy, Clone, Debug)]
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

#[derive(Copy, Clone, Debug)]
pub enum UnaryOperator {
    Not,
    Negate,
}

impl Parser {
    pub fn parse(&self, lexer: &mut Lexer) -> TranslationUnit {
        lexer.reset();
        lexer.lex().expect("LUL");
        Self::translation_unit(lexer)
    }

    fn binop(lexer: &mut Lexer, op_matcher: fn(&TokenKind) -> BinaryOperator) -> BinaryOperator {
        let operator = lexer.token().expect("Failed to get token");
        let kind = &operator.kind;
        let op = op_matcher(kind);
        lexer.consume_token();
        op
    }

    fn unop(lexer: &mut Lexer, op_matcher: fn(&TokenKind) -> UnaryOperator) -> UnaryOperator {
        let operator = lexer.token().expect("Failed to get token");
        let kind = &operator.kind;
        let op = op_matcher(kind);
        lexer.consume_token();
        op
    }

    fn translation_unit(lexer: &mut Lexer) -> TranslationUnit {
        let mut functions = Vec::<Function>::new();
        let mut variables = Vec::<Statement>::new();
        loop {
            if let Some(function) = Self::function(lexer) {
                functions.push(function);
            } else if let Some(variable_declaration) = Self::variable_declaration(lexer) {
                variables.push(variable_declaration);
            } else {
                break;
            }
        }
        TranslationUnit {
            functions,
            variables,
        }
    }

    fn variable_declaration(lexer: &mut Lexer) -> Option<Statement> {
        Self::match_token_maybe(lexer, TokenKind::LetKeyword)?;

        let identifier = Self::match_token(lexer, TokenKind::Identifier, "Expected identifier");
        Self::match_token(lexer, TokenKind::Colon, "Expected \":\"");
        let data_type = Self::data_type(lexer)?;
        let statement = if Self::match_token_maybe(lexer, TokenKind::Equal).is_some() {
            let expression = Self::match_something(lexer, Self::expression, "Expected expression");
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

        Self::match_token(lexer, TokenKind::Semicolon, "Expected \";\"");
        Some(statement)
    }

    fn function(lexer: &mut Lexer) -> Option<Function> {
        Self::match_token_maybe(lexer, TokenKind::FUNcKeyword)?;

        let identifier = Self::match_token(lexer, TokenKind::Identifier, "Expected identifier");
        Self::match_token(lexer, TokenKind::OpenParen, "Expected \"(\"");
        let parameters = Self::parameters(lexer);
        Self::match_token(lexer, TokenKind::CloseParen, "Expected \")\"");
        Self::match_token(lexer, TokenKind::Colon, "Expected \":\"");
        let return_type = Self::match_something(lexer, Self::data_type, "Expected data type");
        let block = Self::match_something(lexer, Self::block, "Expected block");

        Some(Function {
            identifier,
            return_type,
            parameters,
            block,
        })
    }

    fn parameters(lexer: &mut Lexer) -> Vec<Parameter> {
        let mut parameters = Vec::<Parameter>::new();
        while let Some(parameter) = Self::parameter(lexer) {
            parameters.push(parameter);
            if !Self::matches_token_kind(lexer, TokenKind::Comma) {
                break;
            }
            lexer.consume_token();
        }
        parameters
    }

    fn parameter(lexer: &mut Lexer) -> Option<Parameter> {
        let identifier = Self::match_token_maybe(lexer, TokenKind::Identifier)?;
        Self::match_token(lexer, TokenKind::Colon, "Expected \":\"");
        let data_type = Self::match_something(lexer, Self::data_type, "Expected data type");
        Some(Parameter {
            identifier,
            data_type,
        })
    }

    fn block(lexer: &mut Lexer) -> Option<Block> {
        Self::match_token_maybe(lexer, TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement>::new();
        while let Some(statement) = Self::statement(lexer) {
            statements.push(statement);
        }
        Self::match_token(lexer, TokenKind::CloseBrace, "Expected \"}}\"");

        Some(Block { statements })
    }

    fn statement(lexer: &mut Lexer) -> Option<Statement> {
        if let Some(variable_declaration) = Self::variable_declaration(lexer) {
            return Some(variable_declaration);
        } else if Self::match_token_maybe(lexer, TokenKind::IfKeyword).is_some() {
            Self::match_token(lexer, TokenKind::OpenParen, "Expected \"(\"");
            let expression = Self::match_something(lexer, Self::expression, "Expected expression");
            Self::match_token(lexer, TokenKind::CloseParen, "Expected \")\"");

            let statement = Self::match_something(lexer, Self::statement, "Expected statement");
            return if Self::match_token_maybe(lexer, TokenKind::ElseKeyword).is_some() {
                let else_statement =
                    Self::match_something(lexer, Self::statement, "Expected statement");
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
        } else if let Some(block) = Self::block(lexer) {
            return Some(Statement::BlockStatement {
                block: Box::new(block),
            });
        } else if Self::match_token_maybe(lexer, TokenKind::ByeKeyword).is_some() {
            let expression = Self::match_something(lexer, Self::expression, "Expected expression");
            Self::match_token(lexer, TokenKind::Semicolon, "Expected \";\"");

            return Some(Statement::ReturnStatement { expression });
        } else if let Some(expression) = Self::expression(lexer) {
            Self::match_token(lexer, TokenKind::Semicolon, "Expected \";\"");

            return Some(Statement::ExpressionStatement { expression });
        }

        None
    }

    fn data_type(lexer: &mut Lexer) -> Option<DataType> {
        if let Some(token) = lexer.token() {
            return match token.kind {
                TokenKind::PpType => {
                    lexer.consume_token();
                    Some(DataType::Pp)
                }
                _ => Self::struct_(lexer),
            };
        }
        None
    }

    fn struct_(_lexer: &mut Lexer) -> Option<DataType> {
        todo!()
    }

    fn expression(lexer: &mut Lexer) -> Option<Expression> {
        Self::equality(lexer)
    }

    fn equality(lexer: &mut Lexer) -> Option<Expression> {
        let mut expression = Self::comparison(lexer);

        while Self::matches_token_kind(lexer, TokenKind::BangEqual)
            || Self::matches_token_kind(lexer, TokenKind::EqualEqual)
        {
            if expression.is_some() {
                let op = Self::binop(lexer, |kind| match kind {
                    TokenKind::BangEqual => BinaryOperator::NotEqual,
                    TokenKind::EqualEqual => BinaryOperator::Equal,
                    _ => unreachable!(),
                });
                if let Some(rhs) = Self::comparison(lexer) {
                    expression = Some(Expression::BinaryExpression {
                        lhs: Box::new(expression.unwrap()),
                        op,
                        rhs: Box::new(rhs),
                    });
                }
            }
        }
        expression
    }

    fn comparison(lexer: &mut Lexer) -> Option<Expression> {
        let mut expression = Self::term(lexer);

        while Self::matches_token_kind(lexer, TokenKind::Greater)
            || Self::matches_token_kind(lexer, TokenKind::GreaterEqual)
            || Self::matches_token_kind(lexer, TokenKind::Less)
            || Self::matches_token_kind(lexer, TokenKind::LessEqual)
        {
            if expression.is_some() {
                let op = Self::binop(lexer, |kind| match kind {
                    TokenKind::Greater => BinaryOperator::GreaterThan,
                    TokenKind::GreaterEqual => BinaryOperator::GreaterThanOrEqual,
                    TokenKind::Less => BinaryOperator::LessThan,
                    TokenKind::LessEqual => BinaryOperator::LessThanOrEqual,
                    _ => unreachable!(),
                });
                let rhs = Self::match_something(lexer, Self::term, "Expected expression");
                expression = Some(Expression::BinaryExpression {
                    lhs: Box::new(expression.unwrap()),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }
        expression
    }

    fn term(lexer: &mut Lexer) -> Option<Expression> {
        let mut expression = Self::factor(lexer);

        while Self::matches_token_kind(lexer, TokenKind::Dash)
            || Self::matches_token_kind(lexer, TokenKind::Plus)
        {
            if expression.is_some() {
                let op = Self::binop(lexer, |kind| match kind {
                    TokenKind::Dash => BinaryOperator::Subtract,
                    TokenKind::Plus => BinaryOperator::Add,
                    _ => unreachable!(),
                });
                if let Some(factor) = Self::factor(lexer) {
                    expression = Some(Expression::BinaryExpression {
                        lhs: Box::new(expression.unwrap()),
                        op,
                        rhs: Box::new(factor),
                    });
                }
            }
        }

        expression
    }

    fn factor(lexer: &mut Lexer) -> Option<Expression> {
        let mut expression = Self::unary(lexer);

        while Self::matches_token_kind(lexer, TokenKind::ForwardSlash)
            || Self::matches_token_kind(lexer, TokenKind::Star)
        {
            if expression.is_some() {
                let op = Self::binop(lexer, |kind| match kind {
                    TokenKind::ForwardSlash => BinaryOperator::Divide,
                    TokenKind::Star => BinaryOperator::Multiply,
                    _ => unreachable!(),
                });
                if let Some(unary) = Self::unary(lexer) {
                    expression = Some(Expression::BinaryExpression {
                        lhs: Box::new(expression.unwrap()),
                        op,
                        rhs: Box::new(unary),
                    });
                }
            }
        }
        expression
    }

    fn unary(lexer: &mut Lexer) -> Option<Expression> {
        if Self::matches_token_kind(lexer, TokenKind::Bang)
            || Self::matches_token_kind(lexer, TokenKind::Dash)
        {
            let op = Self::unop(lexer, |kind| match kind {
                TokenKind::Bang => UnaryOperator::Not,
                TokenKind::Dash => UnaryOperator::Negate,
                _ => unreachable!(),
            });
            if let Some(unary) = Self::unary(lexer) {
                return Some(Expression::UnaryExpression {
                    op,
                    operand: Box::new(unary),
                });
            }
        }

        Self::primary(lexer)
    }

    fn primary(lexer: &mut Lexer) -> Option<Expression> {
        if let Some(identifier) = Self::match_token_maybe(lexer, TokenKind::Identifier) {
            return if Self::match_token_maybe(lexer, TokenKind::OpenParen).is_some() {
                let arguments = Self::arguments(lexer);
                Self::match_token(lexer, TokenKind::CloseParen, "Expected \")\"");

                Some(Expression::FunctionCall { arguments })
            } else if Self::match_token_maybe(lexer, TokenKind::Equal).is_some() {
                let expression =
                    Self::match_something(lexer, Self::expression, "Expected expression");
                Some(Expression::AssignmentExpression {
                    expression: Box::new(expression),
                })
            } else {
                Some(Expression::IdentifierExpression { identifier })
            };
        } else if Self::match_token_maybe(lexer, TokenKind::NomKeyword).is_some() {
            return Some(Expression::BoobaExpression(false));
        } else if Self::match_token_maybe(lexer, TokenKind::YemKeyword).is_some() {
            return Some(Expression::BoobaExpression(true));
        } else if let Some(number) = Self::match_token_maybe(lexer, TokenKind::Number) {
            return Some(Expression::PpExpression(number.parse::<i32>().unwrap()));
        } else if let Some(fiber) = Self::match_token_maybe(lexer, TokenKind::Fiber) {
            return Some(Expression::FiberExpression(fiber));
        } else if Self::match_token_maybe(lexer, TokenKind::OpenParen).is_some() {
            let expression = Self::match_something(lexer, Self::expression, "Expected expression");
            Self::match_token(lexer, TokenKind::CloseParen, "Expected \")\"");
            return Some(expression);
        }

        None
    }

    fn arguments(lexer: &mut Lexer) -> Vec<Expression> {
        let mut args = Vec::<Expression>::new();
        while let Some(expression) = Self::expression(lexer) {
            args.push(expression);
            if !Self::matches_token_kind(lexer, TokenKind::Comma) {
                break;
            }
            lexer.consume_token();
        }

        args
    }

    fn matches_token_kind(lexer: &Lexer, token_kind: TokenKind) -> bool {
        if let Some(token) = lexer.token() {
            return token.kind == token_kind;
        }
        false
    }

    fn match_token_maybe(lexer: &mut Lexer, token_kind: TokenKind) -> Option<String> {
        if let Some(token) = lexer.token() {
            if token.kind == token_kind {
                let token_value = token.value();
                lexer.consume_token();
                return token_value;
            }
        }

        None
    }

    fn match_token(lexer: &mut Lexer, token_kind: TokenKind, error_message: &str) -> String {
        if let Some(token) = lexer.token() {
            if token.kind == token_kind {
                let token_value = token.value();
                lexer.consume_token();
                if let Some(token_value) = token_value {
                    return token_value;
                }
                return String::new();
            }
        }
        panic!("{}", error_message)
    }

    fn match_something<T>(
        lexer: &mut Lexer,
        grammar_func: fn(&mut Lexer) -> Option<T>,
        error_message: &str,
    ) -> T {
        if let Some(ret_from_something) = grammar_func(lexer) {
            return ret_from_something;
        }
        panic!("{}", error_message)
    }
}
