use crate::lexer::{Lexer, TokenKind};

#[derive(Default)]
pub struct Parser;

#[derive(Debug)]
pub enum Statement {
    VariableDeclaration {
        identifier: String,
        data_type: DataType,
    },
    VariableInitialization {
        identifier: String,
        expression: Expression,
    },
    VariableDeclarationAndInitialization {
        identifier: String,
        data_type: DataType,
        expression: Expression,
    },
    IfStatement {
        expression: Expression,
        block: Box<Block>,
    },
}

#[derive(Debug)]
pub enum TranslationUnit {
    TranslationUnit {
        functions: Vec<Function>,
        variables: Vec<Statement>,
    },
}

#[derive(Debug)]
pub enum Function {
    Function {
        identifier: String,
        return_type: DataType,
        parameters: Vec<Parameter>,
        block: Block,
    },
}
#[derive(Debug)]
pub enum Parameters {
    Parameters(Vec<Parameter>),
}

#[derive(Debug)]
pub enum Parameter {
    Parameter {
        identifier: String,
        data_type: DataType,
    },
}

#[derive(Debug)]
pub enum Block {
    Statements(Vec<Statement>),
}

#[derive(Debug)]
pub enum Expression {
    PpExpression(i32),
    BoobaExpression(bool),
    FiberExpression(String),
    UnaryExpression {
        op: Op,
        operand: Box<Expression>,
    },
    BinaryExpression {
        lhs: Box<Expression>,
        op: Op,
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
pub enum Op {
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
    Not,
    Negate,
}

impl Parser {
    pub fn parse(&self, lexer: &mut Lexer) -> TranslationUnit {
        lexer.reset();
        lexer.lex().expect("LUL");
        Self::translation_unit(lexer)
    }

    fn op(lexer: &mut Lexer, op_matcher: fn(&TokenKind) -> Op) -> Op {
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
        TranslationUnit::TranslationUnit {
            functions,
            variables,
        }
    }

    fn variable_declaration_common(lexer: &mut Lexer) -> Option<(String, DataType)> {
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
            |data_type| Some((identifier, data_type)),
        )
    }

    fn variable_declaration(
        lexer: &mut Lexer,
        var_decl_common: Option<(String, DataType)>,
    ) -> Option<Statement> {
        var_decl_common.as_ref()?;

        let x = var_decl_common.unwrap();
        if !Self::matches_token_kind(lexer, TokenKind::Semicolon) {
            return None;
        }
        lexer.consume_token();

        Some(Statement::VariableDeclaration {
            identifier: x.0,
            data_type: x.1,
        })
    }

    fn variable_declaration_and_assignment(
        lexer: &mut Lexer,
        var_decl_common: Option<(String, DataType)>,
    ) -> Option<Statement> {
        var_decl_common.as_ref()?;

        if !Self::matches_token_kind(lexer, TokenKind::Equal) {
            return None;
        }
        lexer.consume_token();

        let x = var_decl_common.unwrap();
        if let Some(expression) = Self::expression(lexer) {
            assert!(
                Self::matches_token_kind(lexer, TokenKind::Semicolon),
                "Expected \";\""
            );
            lexer.consume_token();
            return Some(Statement::VariableDeclarationAndInitialization {
                identifier: x.0,
                data_type: x.1,
                expression,
            });
        }
        None
    }

    fn functions(lexer: &mut Lexer) -> Vec<Function> {
        let mut functions = Vec::<Function>::new();
        while let Some(function) = Self::function(lexer) {
            functions.push(function);
        }
        functions
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
                return Some(Function::Function {
                    identifier,
                    return_type,
                    parameters,
                    block,
                });
            }
        } else {
            panic!("Expected data type");
        }

        panic!("Not implemented");
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
                Some(Parameter::Parameter {
                    identifier,
                    data_type,
                })
            },
        )
    }

    fn block(lexer: &mut Lexer) -> Option<Block> {
        if Self::matches_token_kind(lexer, TokenKind::OpenBrace) {
            lexer.consume_token();
            if let Some(statement) = Self::statement(lexer) {
                let mut statements = Vec::<Statement>::new();
                statements.push(statement);

                while let Some(statement) = Self::statement(lexer) {
                    statements.push(statement);
                }

                assert!(
                    Self::matches_token_kind(lexer, TokenKind::CloseBrace),
                    "Expected closing brace"
                );
                lexer.consume_token();

                return Some(Block::Statements(statements));
            }
        }

        None
    }

    fn statement(lexer: &mut Lexer) -> Option<Statement> {
        if Self::matches_token_kind(lexer, TokenKind::LetKeyword) {
            lexer.consume_token();
            assert!(
                Self::matches_token_kind(lexer, TokenKind::Identifier),
                "Expected identifier"
            );

            let identifier = lexer.token().unwrap().value.as_ref().unwrap().to_string();
            lexer.consume_token();

            assert!(
                Self::matches_token_kind(lexer, TokenKind::Colon),
                "Expected \":\""
            );
            lexer.consume_token();

            if let Some(data_type) = Self::data_type(lexer) {
                if Self::matches_token_kind(lexer, TokenKind::Equal) {
                    lexer.consume_token();
                    if let Some(expression) = Self::expression(lexer) {
                        assert!(
                            Self::matches_token_kind(lexer, TokenKind::Semicolon),
                            "Expected \";\""
                        );
                        lexer.consume_token();

                        return Some(Statement::VariableDeclarationAndInitialization {
                            identifier,
                            data_type,
                            expression,
                        });
                    }
                } else if Self::matches_token_kind(lexer, TokenKind::Semicolon) {
                    lexer.consume_token();
                    return Some(Statement::VariableDeclaration {
                        identifier,
                        data_type,
                    });
                } else {
                    panic!("Expected \";\"")
                }
            } else {
                panic!("Expected data type")
            }
        } else if Self::matches_token_kind(lexer, TokenKind::Identifier) {
            let identifier = lexer.token().unwrap().value.as_ref().unwrap().to_string();
            lexer.consume_token();

            if Self::matches_token_kind(lexer, TokenKind::Equal) {
                lexer.consume_token();
                if let Some(expression) = Self::expression(lexer) {
                    assert!(
                        Self::matches_token_kind(lexer, TokenKind::Semicolon),
                        "Expected \";\""
                    );
                    lexer.consume_token();

                    return Some(Statement::VariableInitialization {
                        identifier,
                        expression,
                    });
                }
            } else {
                panic!("Expected \"=\"")
            }
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
                let op = Self::op(lexer, |kind| match kind {
                    TokenKind::BangEqual => Op::NotEqual,
                    TokenKind::EqualEqual => Op::Equal,
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
                let op = Self::op(lexer, |kind| match kind {
                    TokenKind::Greater => Op::GreaterThan,
                    TokenKind::GreaterEqual => Op::GreaterThanOrEqual,
                    TokenKind::Less => Op::LessThan,
                    TokenKind::LessEqual => Op::LessThanOrEqual,
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
                let op = Self::op(lexer, |kind| match kind {
                    TokenKind::Dash => Op::Subtract,
                    TokenKind::Plus => Op::Add,
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
                let op = Self::op(lexer, |kind| match kind {
                    TokenKind::ForwardSlash => Op::Divide,
                    TokenKind::Star => Op::Multiply,
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
            let op = Self::op(lexer, |kind| match kind {
                TokenKind::Bang => Op::Not,
                TokenKind::Dash => Op::Negate,
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
