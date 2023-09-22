use std::fmt::Debug;

use crate::lexer::{Lexer, TokenKind};

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
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
    pub fn new(lexer: Lexer) -> Self {
        Self { lexer }
    }

    pub fn parse(&mut self) -> TranslationUnit {
        self.lexer.reset();
        self.lexer.lex().expect("LUL");
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
            } else {
                break;
            }
        }
        TranslationUnit {
            functions,
            variables,
        }
    }

    fn function(&mut self) -> Option<Function> {
        self.match_token_maybe(TokenKind::FUNcKeyword)?;

        let identifier = self.match_token(TokenKind::Identifier, "Expected identifier");
        self.match_token(TokenKind::OpenParen, "Expected \"(\"");
        let parameters = self.parameters();
        self.match_token(TokenKind::CloseParen, "Expected \")\"");
        self.match_token(TokenKind::Colon, "Expected \":\"");
        let return_type = self.match_something(Self::data_type, "Expected data type");
        let block = self.match_something(Self::block, "Expected block");

        Some(Function {
            identifier,
            return_type,
            parameters,
            block,
        })
    }

    fn variable_declaration(&mut self) -> Option<Statement> {
        self.match_token_maybe(TokenKind::LetKeyword)?;

        let identifier = self.match_token(TokenKind::Identifier, "Expected identifier");
        self.match_token(TokenKind::Colon, "Expected \":\"");
        let data_type = self.data_type()?;
        let statement = if self.match_token_maybe(TokenKind::Equal).is_some() {
            let expression = self.match_something(Self::expression, "Expected expression");
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

        self.match_token(TokenKind::Semicolon, "Expected \";\"");
        Some(statement)
    }

    fn binop(&mut self, op_matcher: fn(&TokenKind) -> BinaryOperator) -> BinaryOperator {
        let lexer = &mut self.lexer;
        let operator = lexer.token().expect("Failed to get token");
        let kind = &operator.kind;
        let op = op_matcher(kind);
        lexer.consume_token();
        op
    }

    fn unop(&mut self, op_matcher: fn(&TokenKind) -> UnaryOperator) -> UnaryOperator {
        let lexer = &mut self.lexer;
        let operator = lexer.token().expect("Failed to get token");
        let kind = &operator.kind;
        let op = op_matcher(kind);
        lexer.consume_token();
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
        self.match_token(TokenKind::Colon, "Expected \":\"");
        let data_type = self.match_something(Self::data_type, "Expected data type");
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
        self.match_token(TokenKind::CloseBrace, "Expected \"}}\"");

        Some(Block { statements })
    }

    fn statement(&mut self) -> Option<Statement> {
        if let Some(variable_declaration) = self.variable_declaration() {
            return Some(variable_declaration);
        } else if self.match_token_maybe(TokenKind::IfKeyword).is_some() {
            self.match_token(TokenKind::OpenParen, "Expected \"(\"");
            let expression = self.match_something(Self::expression, "Expected expression");
            self.match_token(TokenKind::CloseParen, "Expected \")\"");

            let statement = self.match_something(
                Self::statement,
                "Expected \
            statement",
            );
            return if self.match_token_maybe(TokenKind::ElseKeyword).is_some() {
                let else_statement = self.match_something(Self::statement, "Expected statement");
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
            let expression = self.match_something(Self::expression, "Expected expression");
            self.match_token(TokenKind::Semicolon, "Expected \";\"");

            return Some(Statement::ReturnStatement { expression });
        } else if let Some(expression) = self.expression() {
            self.match_token(TokenKind::Semicolon, "Expected \";\"");

            return Some(Statement::ExpressionStatement { expression });
        }

        None
    }

    fn data_type(&mut self) -> Option<DataType> {
        let lexer = &mut self.lexer;
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

    fn expression(&mut self) -> Option<Expression> {
        self.equality()
    }

    fn equality(&mut self) -> Option<Expression> {
        let mut expression = self.comparison();

        while self.matches_token_kind(TokenKind::BangEqual)
            || self.matches_token_kind(TokenKind::EqualEqual)
        {
            if expression.is_some() {
                let op = self.binop(|kind| match kind {
                    TokenKind::BangEqual => BinaryOperator::NotEqual,
                    TokenKind::EqualEqual => BinaryOperator::Equal,
                    _ => unreachable!(),
                });
                if let Some(rhs) = self.comparison() {
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

    fn comparison(&mut self) -> Option<Expression> {
        let mut expression = self.term();

        while self.matches_token_kind(TokenKind::Greater)
            || self.matches_token_kind(TokenKind::GreaterEqual)
            || self.matches_token_kind(TokenKind::Less)
            || self.matches_token_kind(TokenKind::LessEqual)
        {
            if expression.is_some() {
                let op = self.binop(|kind| match kind {
                    TokenKind::Greater => BinaryOperator::GreaterThan,
                    TokenKind::GreaterEqual => BinaryOperator::GreaterThanOrEqual,
                    TokenKind::Less => BinaryOperator::LessThan,
                    TokenKind::LessEqual => BinaryOperator::LessThanOrEqual,
                    _ => unreachable!(),
                });
                let rhs = self.match_something(Self::term, "Expected expression");
                expression = Some(Expression::BinaryExpression {
                    lhs: Box::new(expression.unwrap()),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }
        expression
    }

    fn term(&mut self) -> Option<Expression> {
        let mut expression = self.factor();

        while self.matches_token_kind(TokenKind::Dash) || self.matches_token_kind(TokenKind::Plus) {
            if expression.is_some() {
                let op = self.binop(|kind| match kind {
                    TokenKind::Dash => BinaryOperator::Subtract,
                    TokenKind::Plus => BinaryOperator::Add,
                    _ => unreachable!(),
                });
                if let Some(factor) = self.factor() {
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
                if let Some(unary) = self.unary() {
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

    fn unary(&mut self) -> Option<Expression> {
        if self.matches_token_kind(TokenKind::Bang) || self.matches_token_kind(TokenKind::Dash) {
            let op = self.unop(|kind| match kind {
                TokenKind::Bang => UnaryOperator::Not,
                TokenKind::Dash => UnaryOperator::Negate,
                _ => unreachable!(),
            });
            if let Some(unary) = self.unary() {
                return Some(Expression::UnaryExpression {
                    op,
                    operand: Box::new(unary),
                });
            }
        }

        self.primary()
    }

    fn primary(&mut self) -> Option<Expression> {
        if let Some(identifier) = self.match_token_maybe(TokenKind::Identifier) {
            return if self.match_token_maybe(TokenKind::OpenParen).is_some() {
                let arguments = self.arguments();
                self.match_token(TokenKind::CloseParen, "Expected \")\"");

                Some(Expression::FunctionCall { arguments })
            } else if self.match_token_maybe(TokenKind::Equal).is_some() {
                let expression = self.match_something(Self::expression, "Expected expression");
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
        } else if let Some(fiber) = self.match_token_maybe(TokenKind::Fiber) {
            return Some(Expression::FiberExpression(fiber));
        } else if self.match_token_maybe(TokenKind::OpenParen).is_some() {
            let expression = self.match_something(Self::expression, "Expected expression");
            self.match_token(TokenKind::CloseParen, "Expected \")\"");
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

    fn matches_token_kind(&self, token_kind: TokenKind) -> bool {
        let lexer = &self.lexer;
        if let Some(token) = lexer.token() {
            return token.kind == token_kind;
        }
        false
    }

    fn match_token_maybe(&mut self, token_kind: TokenKind) -> Option<String> {
        let lexer = &mut self.lexer;
        if let Some(token) = lexer.token() {
            if token.kind == token_kind {
                let token_value = token.value();
                lexer.consume_token();
                return token_value;
            }
        }

        None
    }

    fn match_token(&mut self, token_kind: TokenKind, error_message: &str) -> String {
        let lexer = &mut self.lexer;
        if let Some(token) = lexer.token() {
            if token.kind == token_kind {
                let token_value = token.value();
                lexer.consume_token();
                if let Some(token_value) = token_value {
                    return token_value;
                }
            }
            if let Some(prev_token) = lexer.token_lookahead(-1) {
                let row = prev_token.row();
                let col = prev_token.col() + 1;
                self.lexer
                    .error_diag()
                    .handle_error_at(row, col, error_message);
            } else {
                self.lexer.error_diag().handle("No token found");
            }
        }
        return String::new();
    }

    fn match_something<T>(
        &mut self,
        grammar_func: fn(&mut Parser) -> Option<T>,
        error_message: &str,
    ) -> T {
        if let Some(ret_from_something) = grammar_func(self) {
            return ret_from_something;
        }
        panic!("{}", error_message)
    }
    pub fn lexer(&self) -> &Lexer {
        &self.lexer
    }
}
