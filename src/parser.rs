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
    VariableAssignment {
        identifier: String,
        expression: Expression,
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
    ReturnStatement {
        expression: Expression,
    },
    BlockStatement {
        block: Box<Block>,
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
            let variable_decl_common = Self::variable_declaration_common(lexer);
            if let Some(function) = Self::function(lexer) {
                functions.push(function);
            } else if let Some(variable_declaration) =
                Self::variable_declaration(lexer, variable_decl_common.clone())
            {
                variables.push(variable_declaration);
            } else if let Some(variable_declaration_and_assignment) =
                Self::variable_declaration_and_assignment(lexer, variable_decl_common)
            {
                variables.push(variable_declaration_and_assignment);
            } else {
                break;
            }
        }
        TranslationUnit {
            functions,
            variables,
        }
    }

    fn variable_declaration_common(lexer: &mut Lexer) -> Option<Variable> {
        if !Self::matches_token_kind(lexer, TokenKind::LetKeyword) {
            return None;
        }
        lexer.consume_token();

        assert!(
            Self::matches_token_kind(lexer, TokenKind::Identifier),
            "Expected identifier"
        );
        let identifier = lexer.token_value().unwrap();
        lexer.consume_token();

        assert!(
            Self::matches_token_kind(lexer, TokenKind::Colon),
            "Expected \":\""
        );
        lexer.consume_token();

        Self::data_type(lexer).map_or_else(
            || panic!("Expected data type"),
            |data_type| {
                Some(Variable {
                    identifier,
                    data_type,
                })
            },
        )
    }

    fn variable_assignment(lexer: &mut Lexer) -> Option<Statement> {
        if !Self::matches_token_kind(lexer, TokenKind::Identifier) {
            return None;
        }
        let identifier = lexer.token_value().unwrap();
        lexer.consume_token();

        if !Self::matches_token_kind(lexer, TokenKind::Equal) {
            return None;
        }
        lexer.consume_token();
        let statement = Self::expression(lexer).map_or_else(
            || {
                panic!("Expression expected");
            },
            |expression| {
                assert!(
                    Self::matches_token_kind(lexer, TokenKind::Semicolon),
                    "Expected \";\""
                );
                lexer.consume_token();

                Statement::VariableAssignment {
                    identifier,
                    expression,
                }
            },
        );
        Some(statement)
    }

    fn variable_declaration(
        lexer: &mut Lexer,
        var_decl_common: Option<Variable>,
    ) -> Option<Statement> {
        var_decl_common.as_ref()?;

        if !Self::matches_token_kind(lexer, TokenKind::Semicolon) {
            return None;
        }
        lexer.consume_token();

        let Variable {
            identifier,
            data_type,
        } = var_decl_common.unwrap();
        Some(Statement::VariableDeclaration {
            identifier,
            data_type,
        })
    }

    fn variable_declaration_and_assignment(
        lexer: &mut Lexer,
        var_decl_common: Option<Variable>,
    ) -> Option<Statement> {
        var_decl_common.as_ref()?;

        if !Self::matches_token_kind(lexer, TokenKind::Equal) {
            return None;
        }
        lexer.consume_token();

        let Variable {
            identifier,
            data_type,
        } = var_decl_common.unwrap();
        if let Some(expression) = Self::expression(lexer) {
            assert!(
                Self::matches_token_kind(lexer, TokenKind::Semicolon),
                "Expected \";\""
            );
            lexer.consume_token();
            return Some(Statement::VariableDeclarationAndAssignment {
                identifier,
                data_type,
                expression,
            });
        };
        panic!("Expected expression")
    }

    fn function(lexer: &mut Lexer) -> Option<Function> {
        if !Self::matches_token_kind(lexer, TokenKind::FUNcKeyword) {
            return None;
        }
        lexer.consume_token();
        assert!(
            Self::matches_token_kind(lexer, TokenKind::Identifier),
            "Expected identifier"
        );
        let identifier = lexer.token_value().unwrap();
        lexer.consume_token();

        assert!(
            Self::matches_token_kind(lexer, TokenKind::OpenParen),
            "Expected \"(\""
        );
        lexer.consume_token();

        let parameters = Self::parameters(lexer);
        assert!(
            Self::matches_token_kind(lexer, TokenKind::CloseParen),
            "Expected \")\""
        );
        lexer.consume_token();

        assert!(
            Self::matches_token_kind(lexer, TokenKind::Colon),
            "Expected \":\""
        );
        lexer.consume_token();

        if let Some(return_type) = Self::data_type(lexer) {
            if let Some(block) = Self::block(lexer) {
                return Some(Function {
                    identifier,
                    return_type,
                    parameters,
                    block,
                });
            }
            panic!("Expected block")
        } else {
            panic!("Expected data type");
        }
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
                "Expected closing brace"
            );
            lexer.consume_token();

            return Some(Block { statements });
        }

        None
    }

    fn statement(lexer: &mut Lexer) -> Option<Statement> {
        let common = Self::variable_declaration_common(lexer);
        if let Some(variable_declaration) = Self::variable_declaration(lexer, common.clone()) {
            return Some(variable_declaration);
        }
        if let Some(variable_decl_and_assign) =
            Self::variable_declaration_and_assignment(lexer, common)
        {
            return Some(variable_decl_and_assign);
        } else if let Some(variable_assignment) = Self::variable_assignment(lexer) {
            return Some(variable_assignment);
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
                return Some(Statement::ReturnStatement { expression });
            }

            panic!("Expected expression");
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
            let expression = Expression::IdentifierExpression {
                identifier: String::from(lexer.token().unwrap().value.as_ref().unwrap()),
            };
            lexer.consume_token();
            return Some(expression);
        }
        if Self::matches_token_kind(lexer, TokenKind::False) {
            let expression = Expression::BoobaExpression(false);
            lexer.consume_token();
            return Some(expression);
        }
        if Self::matches_token_kind(lexer, TokenKind::True) {
            let expression = Expression::BoobaExpression(true);
            lexer.consume_token();
            return Some(expression);
        }
        if Self::matches_token_kind(lexer, TokenKind::Number) {
            let expression =
                Expression::PpExpression(lexer.token_value().unwrap().parse::<i32>().unwrap());
            lexer.consume_token();
            return Some(expression);
        }
        if Self::matches_token_kind(lexer, TokenKind::String) {
            let expression =
                Expression::FiberExpression(lexer.token_value().unwrap().parse().unwrap());
            lexer.consume_token();
            return Some(expression);
        }
        if Self::matches_token_kind(lexer, TokenKind::OpenParen) {
            lexer.consume_token();
            let expression = Self::expression(lexer);
            assert!(
                Self::matches_token_kind(lexer, TokenKind::CloseParen),
                "Expected closing parenthesis"
            );
            lexer.consume_token();
            return expression;
        }

        None
    }

    fn matches_token_kind(lexer: &Lexer, token_kind: TokenKind) -> bool {
        if let Some(token) = lexer.token() {
            return token.kind == token_kind;
        }
        false
    }
}
