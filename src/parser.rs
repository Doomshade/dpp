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
        block: Box<Block>,
    },
    IfElseStatement {
        expression: Expression,
        block: Box<Block>,
        else_block: Box<Block>,
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

        // I don't know how to style this better besides the bunch
        // of "if-else" stmts :(
        // Maybe create a function that panics?
        if let Some(identifier) = Self::match_token_maybe(lexer, TokenKind::Identifier) {
            if let Some(_) = Self::match_token_maybe(lexer, TokenKind::OpenParen) {
                let parameters = Self::parameters(lexer);

                if let Some(_) = Self::match_token_maybe(lexer, TokenKind::CloseParen) {
                    if let Some(_) = Self::match_token_maybe(lexer, TokenKind::Colon) {
                        if let Some(return_type) = Self::data_type(lexer) {
                            if let Some(block) = Self::block(lexer) {
                                return Some(Function {
                                    identifier,
                                    return_type,
                                    parameters,
                                    block,
                                });
                            } else {
                                panic!("Expected block")
                            }
                        } else {
                            panic!("Expected data type");
                        }
                    } else {
                        panic!("Expected \":\"")
                    }
                } else {
                    panic!("Expected \")\"")
                }
            } else {
                panic!("Expected \"(\"")
            }
        } else {
            panic!("Expected identifier")
        }
    }

    fn identifiers(lexer: &mut Lexer) -> Vec<String> {
        let mut identifiers = Vec::<String>::new();
        while let Some(identifier) = Self::identifier(lexer) {
            identifiers.push(identifier);
            if !Self::matches_token_kind(lexer, TokenKind::Comma) {
                break;
            }
            lexer.consume_token();
        }
        identifiers
    }

    fn identifier(lexer: &mut Lexer) -> Option<String> {
        if Self::matches_token_kind(lexer, TokenKind::Identifier) {
            let option = lexer.token_value();
            lexer.consume_token();
            return option;
        }
        None
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
        if !Self::matches_token_kind(lexer, TokenKind::Identifier) {
            return None;
        }
        let identifier = lexer.token_value().unwrap();
        lexer.consume_token();

        assert!(
            Self::matches_token_kind(lexer, TokenKind::Colon),
            "Expected \":\""
        );
        lexer.consume_token();

        Self::data_type(lexer).map_or_else(
            || {
                panic!("Expected data type");
            },
            |data_type| {
                Some(Parameter {
                    identifier,
                    data_type,
                })
            },
        )
    }

    fn block(lexer: &mut Lexer) -> Option<Block> {
        if Self::matches_token_kind(lexer, TokenKind::OpenBrace) {
            lexer.consume_token();
            let mut statements = Vec::<Statement>::new();
            if let Some(statement) = Self::statement(lexer) {
                statements.push(statement);

                while let Some(statement) = Self::statement(lexer) {
                    statements.push(statement);
                }
            }
            assert!(
                Self::matches_token_kind(lexer, TokenKind::CloseBrace),
                "Expected \"}}\""
            );
            lexer.consume_token();

            return Some(Block { statements });
        }

        None
    }

    fn statement(lexer: &mut Lexer) -> Option<Statement> {
        if let Some(variable_declaration) = Self::variable_declaration(lexer) {
            return Some(variable_declaration);
        } else if Self::matches_token_kind(lexer, TokenKind::IfKeyword) {
            lexer.consume_token();
            assert!(
                Self::matches_token_kind(lexer, TokenKind::OpenParen),
                "Expected \"(\""
            );
            lexer.consume_token();
            if let Some(expression) = Self::expression(lexer) {
                assert!(
                    Self::matches_token_kind(lexer, TokenKind::CloseParen),
                    "Expected \")\""
                );
                lexer.consume_token();
                if let Some(block) = Self::block(lexer) {
                    if Self::matches_token_kind(lexer, TokenKind::ElseKeyword) {
                        lexer.consume_token();
                        if let Some(else_block) = Self::block(lexer) {
                            return Some(Statement::IfElseStatement {
                                expression,
                                block: Box::new(block),
                                else_block: Box::new(else_block),
                            });
                        }
                    }
                    return Some(Statement::IfStatement {
                        expression,
                        block: Box::new(block),
                    });
                }
            }
        } else if let Some(block) = Self::block(lexer) {
            return Some(Statement::BlockStatement {
                block: Box::new(block),
            });
        } else if Self::matches_token_kind(lexer, TokenKind::ByeKeyword) {
            lexer.consume_token();
            if let Some(expression) = Self::expression(lexer) {
                assert!(
                    Self::matches_token_kind(lexer, TokenKind::Semicolon),
                    "Expected \";\""
                );
                lexer.consume_token();
                return Some(Statement::ReturnStatement { expression });
            }

            panic!("Expected expression");
        } else if let Some(expression) = Self::expression(lexer) {
            assert!(
                Self::matches_token_kind(lexer, TokenKind::Semicolon),
                "Expected \";\""
            );
            lexer.consume_token();
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
        panic!("No token")
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
                if let Some(rhs) = Self::term(lexer) {
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
        if Self::matches_token_kind(lexer, TokenKind::Identifier) {
            let identifier = lexer.token_value().unwrap();
            lexer.consume_token();
            if Self::matches_token_kind(lexer, TokenKind::OpenParen) {
                lexer.consume_token();
                let arguments = Self::arguments(lexer);
                assert!(
                    Self::matches_token_kind(lexer, TokenKind::CloseParen),
                    "Expected \")\""
                );
                lexer.consume_token();
                return Some(Expression::FunctionCall { arguments });
            } else if Self::matches_token_kind(lexer, TokenKind::Equal) {
                lexer.consume_token();
                if let Some(expression) = Self::expression(lexer) {
                    return Some(Expression::AssignmentExpression {
                        expression: Box::new(expression),
                    });
                }
                panic!("Expected expression");
            }
            let expression = Expression::IdentifierExpression { identifier };
            return Some(expression);
        } else if Self::matches_token_kind(lexer, TokenKind::NomKeyword) {
            lexer.consume_token();
            return Some(Expression::BoobaExpression(false));
        } else if Self::matches_token_kind(lexer, TokenKind::YemKeyword) {
            lexer.consume_token();
            return Some(Expression::BoobaExpression(true));
        } else if Self::matches_token_kind(lexer, TokenKind::Number) {
            let expression =
                Expression::PpExpression(lexer.token_value().unwrap().parse::<i32>().unwrap());
            lexer.consume_token();
            return Some(expression);
        } else if Self::matches_token_kind(lexer, TokenKind::String) {
            let expression = Expression::FiberExpression(lexer.token_value().unwrap());
            lexer.consume_token();
            return Some(expression);
        } else if Self::matches_token_kind(lexer, TokenKind::OpenParen) {
            lexer.consume_token();
            let expression = Self::expression(lexer);
            assert!(
                Self::matches_token_kind(lexer, TokenKind::CloseParen),
                "Expected \")\""
            );
            lexer.consume_token();
            return expression;
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

    fn match_something<T>(lexer: &mut Lexer, grammar_func: fn(&mut Lexer) -> Option<T>, error_message: &str) -> T {
        if let Some(ret_from_something) = grammar_func(lexer) {
            return ret_from_something;
        }
        panic!("{}", error_message)
    }
}
