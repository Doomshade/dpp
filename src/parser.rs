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
    pub fn parse(&self, lexer: &mut Lexer) -> Vec<Function> {
        lexer.reset();
        lexer.lex().expect("LUL");
        self.functions(lexer)
    }

    fn op(&self, lexer: &mut Lexer, op_matcher: fn(&TokenKind) -> Op) -> Op {
        let operator = lexer.token().expect("Failed to get token");
        let kind = &operator.kind;
        let op = op_matcher(kind);
        lexer.consume_token();
        op
    }

    pub fn print_parse_tree(&self, lexer: &mut Lexer) {
        let program = self.parse(lexer);
        println!("{program:#?}");
    }

    fn translation_unit(&self, lexer: &mut Lexer) -> TranslationUnit {
        let mut functions = Vec::<Function>::new();
        let mut variables = Vec::<Statement>::new();
        loop {
            if let Some(function) = self.function(lexer) {
                functions.push(function);
            } else {
                let variable_decl_common = self.variable_declaration_common(lexer);
                if let Some(variable_declaration) =
                    self.variable_declaration(lexer, variable_decl_common.clone())
                {
                    variables.push(variable_declaration);
                } else if let Some(variable_declaration_and_assignment) =
                    self.variable_declaration_and_assignment(lexer, variable_decl_common)
                {
                    variables.push(variable_declaration_and_assignment);
                } else {
                    break;
                }
            }
        }
        TranslationUnit::TranslationUnit {
            functions,
            variables,
        }
    }

    fn variable_declaration_common(&self, lexer: &mut Lexer) -> Option<(String, DataType)> {
        if !self.matches_token_kind(lexer, TokenKind::LetKeyword) {
            return None;
        }
        lexer.consume_token();

        if !self.matches_token_kind(lexer, TokenKind::Identifier) {
            panic!("Expected identifier")
        }

        let identifier = lexer.token_value().unwrap();
        lexer.consume_token();
        if !self.matches_token_kind(lexer, TokenKind::Colon) {
            panic!("Expected \":\"")
        }
        lexer.consume_token();
        if let Some(data_type) = self.data_type(lexer) {
            Some((identifier, data_type))
        } else {
            panic!("Expected data type")
        }
    }

    fn variable_declaration(
        &self,
        lexer: &mut Lexer,
        var_decl_common: Option<(String, DataType)>,
    ) -> Option<Statement> {
        if let None = var_decl_common {
            return None;
        }
        let x = var_decl_common.unwrap();
        if !self.matches_token_kind(lexer, TokenKind::Semicolon) {
            return None;
        }
        lexer.consume_token();

        Some(Statement::VariableDeclaration {
            identifier: x.0,
            data_type: x.1,
        })
    }

    fn variable_declaration_and_assignment(
        &self,
        lexer: &mut Lexer,
        var_decl_common: Option<(String, DataType)>,
    ) -> Option<Statement> {
        if let None = var_decl_common {
            return None;
        }

        if !self.matches_token_kind(lexer, TokenKind::Equal) {
            return None;
        }
        lexer.consume_token();

        let x = var_decl_common.unwrap();
        if let Some(expression) = self.expression(lexer) {
            return Some(Statement::VariableDeclarationAndInitialization {
                identifier: x.0,
                data_type: x.1,
                expression,
            });
        }
        None
    }

    fn functions(&self, lexer: &mut Lexer) -> Vec<Function> {
        let mut functions = Vec::<Function>::new();
        while let Some(function) = self.function(lexer) {
            functions.push(function);
        }
        functions
    }

    fn function(&self, lexer: &mut Lexer) -> Option<Function> {
        if !self.matches_token_kind(lexer, TokenKind::FUNcKeyword) {
            return None;
        }
        lexer.consume_token();
        assert!(
            self.matches_token_kind(lexer, TokenKind::Identifier),
            "Expected identifier"
        );
        let identifier = lexer.token_value().unwrap();
        lexer.consume_token();

        assert!(
            self.matches_token_kind(lexer, TokenKind::OpenParen),
            "Expected \"(\""
        );
        lexer.consume_token();

        let parameters = self.parameters(lexer);
        assert!(
            self.matches_token_kind(lexer, TokenKind::CloseParen),
            "Expected \")\""
        );
        lexer.consume_token();

        assert!(
            self.matches_token_kind(lexer, TokenKind::Colon),
            "Expected \":\""
        );
        lexer.consume_token();

        if let Some(return_type) = self.data_type(lexer) {
            if let Some(block) = self.block(lexer) {
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

    fn parameters(&self, lexer: &mut Lexer) -> Vec<Parameter> {
        let mut parameters = Vec::<Parameter>::new();
        while let Some(parameter) = self.parameter(lexer) {
            parameters.push(parameter);
            if !self.matches_token_kind(lexer, TokenKind::Comma) {
                break;
            }
            lexer.consume_token();
        }
        parameters
    }

    fn parameter(&self, lexer: &mut Lexer) -> Option<Parameter> {
        if !self.matches_token_kind(lexer, TokenKind::Identifier) {
            return None;
        }
        let identifier = lexer.token_value().unwrap();
        lexer.consume_token();

        assert!(
            self.matches_token_kind(lexer, TokenKind::Colon),
            "Expected \":\""
        );
        lexer.consume_token();

        if let Some(data_type) = self.data_type(lexer) {
            Some(Parameter::Parameter {
                identifier,
                data_type,
            })
        } else {
            panic!("Expected data type");
        }
    }

    fn block(&self, lexer: &mut Lexer) -> Option<Block> {
        if self.matches_token_kind(lexer, TokenKind::OpenBrace) {
            lexer.consume_token();
            if let Some(statement) = self.statement(lexer) {
                let mut statements = Vec::<Statement>::new();
                statements.push(statement);

                while let Some(statement) = self.statement(lexer) {
                    statements.push(statement);
                }

                assert!(
                    self.matches_token_kind(lexer, TokenKind::CloseBrace),
                    "Expected closing brace"
                );
                lexer.consume_token();

                return Some(Block::Statements(statements));
            }
        }

        None
    }

    fn statement(&self, lexer: &mut Lexer) -> Option<Statement> {
        if self.matches_token_kind(lexer, TokenKind::LetKeyword) {
            lexer.consume_token();
            assert!(
                self.matches_token_kind(lexer, TokenKind::Identifier),
                "Expected identifier"
            );

            let identifier = lexer.token().unwrap().value.as_ref().unwrap().to_string();
            lexer.consume_token();

            assert!(
                self.matches_token_kind(lexer, TokenKind::Colon),
                "Expected \":\""
            );
            lexer.consume_token();

            if let Some(data_type) = self.data_type(lexer) {
                if self.matches_token_kind(lexer, TokenKind::Equal) {
                    lexer.consume_token();
                    if let Some(expression) = self.expression(lexer) {
                        assert!(
                            self.matches_token_kind(lexer, TokenKind::Semicolon),
                            "Expected \";\""
                        );
                        lexer.consume_token();

                        return Some(Statement::VariableDeclarationAndInitialization {
                            identifier,
                            data_type,
                            expression,
                        });
                    }
                } else if self.matches_token_kind(lexer, TokenKind::Semicolon) {
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
        } else if self.matches_token_kind(lexer, TokenKind::Identifier) {
            let identifier = lexer.token().unwrap().value.as_ref().unwrap().to_string();
            lexer.consume_token();

            if self.matches_token_kind(lexer, TokenKind::Equal) {
                lexer.consume_token();
                if let Some(expression) = self.expression(lexer) {
                    assert!(
                        self.matches_token_kind(lexer, TokenKind::Semicolon),
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
        } else if self.matches_token_kind(lexer, TokenKind::IfKeyword) {
            lexer.consume_token();
            assert!(
                self.matches_token_kind(lexer, TokenKind::OpenParen),
                "Expected \"(\""
            );
            lexer.consume_token();
            if let Some(expression) = self.expression(lexer) {
                assert!(
                    self.matches_token_kind(lexer, TokenKind::CloseParen),
                    "Expected \")\""
                );
                lexer.consume_token();
                if let Some(block) = self.block(lexer) {
                    return Some(Statement::IfStatement {
                        expression,
                        block: Box::new(block),
                    });
                }
            }
        }

        None
    }

    fn data_type(&self, lexer: &mut Lexer) -> Option<DataType> {
        if let Some(token) = lexer.token() {
            return match token.kind {
                TokenKind::PpType => {
                    lexer.consume_token();
                    Some(DataType::Pp)
                }
                _ => self.struct_(lexer),
            };
        }
        panic!("No token")
    }

    fn struct_(&self, _lexer: &mut Lexer) -> Option<DataType> {
        todo!()
    }

    fn expression(&self, lexer: &mut Lexer) -> Option<Expression> {
        self.equality(lexer)
    }

    fn equality(&self, lexer: &mut Lexer) -> Option<Expression> {
        let mut expression = self.comparison(lexer);

        while self.matches_token_kind(lexer, TokenKind::BangEqual)
            || self.matches_token_kind(lexer, TokenKind::EqualEqual)
        {
            if expression.is_some() {
                let op = self.op(lexer, |kind| match kind {
                    TokenKind::BangEqual => Op::NotEqual,
                    TokenKind::EqualEqual => Op::Equal,
                    _ => unreachable!(),
                });
                if let Some(rhs) = self.comparison(lexer) {
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

    fn comparison(&self, lexer: &mut Lexer) -> Option<Expression> {
        let mut expression = self.term(lexer);

        while self.matches_token_kind(lexer, TokenKind::Greater)
            || self.matches_token_kind(lexer, TokenKind::GreaterEqual)
            || self.matches_token_kind(lexer, TokenKind::Less)
            || self.matches_token_kind(lexer, TokenKind::LessEqual)
        {
            if expression.is_some() {
                let op = self.op(lexer, |kind| match kind {
                    TokenKind::Greater => Op::GreaterThan,
                    TokenKind::GreaterEqual => Op::GreaterThanOrEqual,
                    TokenKind::Less => Op::LessThan,
                    TokenKind::LessEqual => Op::LessThanOrEqual,
                    _ => unreachable!(),
                });
                if let Some(rhs) = self.term(lexer) {
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

    fn term(&self, lexer: &mut Lexer) -> Option<Expression> {
        let mut expression = self.factor(lexer);

        while self.matches_token_kind(lexer, TokenKind::Dash)
            || self.matches_token_kind(lexer, TokenKind::Plus)
        {
            if expression.is_some() {
                let op = self.op(lexer, |kind| match kind {
                    TokenKind::Dash => Op::Subtract,
                    TokenKind::Plus => Op::Add,
                    _ => unreachable!(),
                });
                if let Some(factor) = self.factor(lexer) {
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

    fn factor(&self, lexer: &mut Lexer) -> Option<Expression> {
        let mut expression = self.unary(lexer);

        while self.matches_token_kind(lexer, TokenKind::ForwardSlash)
            || self.matches_token_kind(lexer, TokenKind::Star)
        {
            if expression.is_some() {
                let op = self.op(lexer, |kind| match kind {
                    TokenKind::ForwardSlash => Op::Divide,
                    TokenKind::Star => Op::Multiply,
                    _ => unreachable!(),
                });
                if let Some(unary) = self.unary(lexer) {
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

    fn unary(&self, lexer: &mut Lexer) -> Option<Expression> {
        if self.matches_token_kind(lexer, TokenKind::Bang)
            || self.matches_token_kind(lexer, TokenKind::Dash)
        {
            let op = self.op(lexer, |kind| match kind {
                TokenKind::Bang => Op::Not,
                TokenKind::Dash => Op::Negate,
                _ => unreachable!(),
            });
            if let Some(unary) = self.unary(lexer) {
                return Some(Expression::UnaryExpression {
                    op,
                    operand: Box::new(unary),
                });
            }
        }

        self.primary(lexer)
    }

    fn primary(&self, lexer: &mut Lexer) -> Option<Expression> {
        if self.matches_token_kind(lexer, TokenKind::Identifier) {
            let expression = Expression::IdentifierExpression {
                identifier: String::from(lexer.token().unwrap().value.as_ref().unwrap()),
            };
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::False) {
            let expression = Expression::BoobaExpression(false);
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::True) {
            let expression = Expression::BoobaExpression(true);
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::Number) {
            let expression =
                Expression::PpExpression(lexer.token_value().unwrap().parse::<i32>().unwrap());
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::String) {
            let expression =
                Expression::FiberExpression(lexer.token_value().unwrap().parse().unwrap());
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::OpenParen) {
            lexer.consume_token();
            let expression = self.expression(lexer);
            assert!(
                self.matches_token_kind(lexer, TokenKind::CloseParen),
                "Expected closing parenthesis"
            );
            lexer.consume_token();
            return expression;
        }

        None
    }

    fn matches_token_kind(&self, lexer: &Lexer, token_kind: TokenKind) -> bool {
        if let Some(token) = lexer.token() {
            return token.kind == token_kind;
        }
        false
    }
}
