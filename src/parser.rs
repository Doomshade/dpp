use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::lexer::{Token, TokenKind};

#[derive(Debug)]
pub struct Parser {
    tokens: Rc<Vec<Token>>,
    error_diag: Rc<RefCell<ErrorDiagnosis>>,
    curr_token_index: usize,
    position: (u32, u32),
}

#[derive(Debug, Default, PartialEq, Eq)]
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
    ForiStatement {
        position: (u32, u32),
        index_ident: String,
        length_expression: Expression,
        statement: Box<Statement>,
    },
    #[default]
    InvalidStatement,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum TranslationUnit {
    TranslationUnit {
        functions: Vec<Function>,
        variables: Vec<Statement>,
    },
    #[default]
    InvalidTranslationUnit,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum Function {
    Function {
        position: (u32, u32),
        identifier: String,
        return_type: DataType,
        parameters: Vec<Parameter>,
        block: Block,
    },
    #[default]
    InvalidFunction,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum Parameters {
    Parameters {
        position: (u32, u32),
        parameters: Vec<Parameter>,
    },
    #[default]
    InvalidParameters,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum Parameter {
    Parameter {
        position: (u32, u32),
        identifier: String,
        data_type: DataType,
    },
    #[default]
    InvalidParameter,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum Variable {
    Variable {
        position: (u32, u32),
        identifier: String,
        data_type: DataType,
    },
    #[default]
    InvalidVariable,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum Block {
    Block {
        position: (u32, u32),
        statements: Vec<Statement>,
    },
    #[default]
    InvalidBlock,
}

#[derive(Debug, PartialEq, Default, Eq)]
pub enum Expression {
    PpExpression {
        position: (u32, u32),
        pp: i32,
    },
    BoobaExpression {
        position: (u32, u32),
        booba: bool,
    },
    FiberExpression {
        position: (u32, u32),
        fiber: String,
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
    #[default]
    InvalidExpression,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum DataType {
    Xxlpp,
    Nopp,
    Pp,
    Spp,
    Xspp,
    P,
    Fiber,
    Booba,
    Struct {
        name: String,
    },
    #[default]
    InvalidDataType,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum Struct {
    #[default]
    InvalidStruct,
}

#[derive(Debug, Default, PartialEq, Eq)]
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
    #[default]
    InvalidBinaryOperator,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub enum UnaryOperator {
    Not,
    Negate,
    #[default]
    InvalidUnaryOperator,
}

impl Parser {
    pub fn new(tokens: Rc<Vec<Token>>, error_diag: Rc<RefCell<ErrorDiagnosis>>) -> Self {
        Self {
            position: (1, 1),
            tokens,
            curr_token_index: 0,
            error_diag,
        }
    }

    fn consume_token(&mut self) {
        self.curr_token_index += 1;
        if let Some(token) = self.token() {
            self.position = token.position();
        }
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
        match self.translation_unit() {
            Some(tn) => tn,
            None => panic!(),
        }
    }

    fn translation_unit(&mut self) -> Option<TranslationUnit> {
        let mut functions = Vec::<Function>::new();
        let mut variables = Vec::<Statement>::new();
        loop {
            if let Some(function) = self.is_word(Self::function) {
                functions.push(function);
            } else if let Some(variable_declaration) = self.is_word(Self::variable_declaration) {
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
        Some(TranslationUnit::TranslationUnit {
            functions,
            variables,
        })
    }

    fn function(&mut self) -> Option<Function> {
        let position = self.position;
        self.match_token_maybe(TokenKind::FUNcKeyword)?;

        let identifier = self.match_token(TokenKind::Identifier);
        self.match_token(TokenKind::OpenParen);
        let parameters = self.parameters();
        self.match_token(TokenKind::CloseParen);
        self.match_token(TokenKind::Colon);
        let return_type = self.match_(Self::data_type, "data type");
        let block = self.match_(Self::block, "block");

        Some(Function::Function {
            position,
            identifier,
            return_type,
            parameters,
            block,
        })
    }

    fn variable_declaration(&mut self) -> Option<Statement> {
        let position = self.position;
        self.match_token_maybe(TokenKind::LetKeyword)?;

        let identifier = self.match_token(TokenKind::Identifier);
        self.match_token(TokenKind::Colon);
        let data_type = self.match_(Self::data_type, "data type");
        let statement = if self.match_token_maybe(TokenKind::Equal).is_some() {
            let expression = self.match_(Self::expression, "expression");
            Statement::VariableDeclarationAndAssignment {
                position,
                identifier,
                data_type,
                expression,
            }
        } else {
            Statement::VariableDeclaration {
                position,
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
        let position = self.position;
        let identifier = self.match_token_maybe(TokenKind::Identifier)?;
        self.match_token(TokenKind::Colon);
        let data_type = self.match_(Self::data_type, "data type");
        Some(Parameter::Parameter {
            position,
            identifier,
            data_type,
        })
    }

    fn block(&mut self) -> Option<Block> {
        let position = self.position;
        self.match_token_maybe(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement>::new();
        while let Some(statement) = self.statement() {
            statements.push(statement);
        }
        self.match_token(TokenKind::CloseBrace);

        Some(Block::Block {
            position,
            statements,
        })
    }

    fn statement(&mut self) -> Option<Statement> {
        let position = self.position;
        if let Some(variable_declaration) = self.variable_declaration() {
            return Some(variable_declaration);
        } else if self.match_token_maybe(TokenKind::IfKeyword).is_some() {
            self.match_token(TokenKind::OpenParen);
            let expression = self.match_(Self::expression, "expression");
            self.match_token(TokenKind::CloseParen);

            let statement = self.match_(Self::statement, "statement");
            return if self.match_token_maybe(TokenKind::ElseKeyword).is_some() {
                let else_statement = self.match_(Self::statement, "statement");
                Some(Statement::IfElseStatement {
                    position,
                    expression,
                    statement: Box::new(statement),
                    else_statement: Box::new(else_statement),
                })
            } else {
                Some(Statement::IfStatement {
                    position,
                    expression,
                    statement: Box::new(statement),
                })
            };
        } else if self.match_token_maybe(TokenKind::ForiKeyword).is_some() {
            self.match_token(TokenKind::OpenParen);
            let ident = self.match_token(TokenKind::Identifier);
            self.match_token(TokenKind::Comma);
            let expression = self.match_(Self::expression, "expression");
            self.match_token(TokenKind::CloseParen);
            let statement = self.match_(Self::statement, "statement");

            return Some(Statement::ForiStatement {
                position,
                index_ident: ident,
                length_expression: expression,
                statement: Box::new(statement),
            });
        } else if let Some(block) = self.block() {
            return Some(Statement::BlockStatement {
                position,
                block: Box::new(block),
            });
        } else if self.match_token_maybe(TokenKind::ByeKeyword).is_some() {
            let expression = self.match_(Self::expression, "expression");
            self.match_token(TokenKind::Semicolon);

            return Some(Statement::ReturnStatement {
                position,
                expression,
            });
        } else if let Some(expression) = self.expression() {
            self.match_token(TokenKind::Semicolon);

            return Some(Statement::ExpressionStatement {
                position,
                expression,
            });
        } else if self.match_token_maybe(TokenKind::Semicolon).is_some() {
            return Some(Statement::EmptyStatement { position });
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
                TokenKind::PType => {
                    self.consume_token();
                    Some(DataType::P)
                }
                TokenKind::XsppType => {
                    self.consume_token();
                    Some(DataType::Xspp)
                }
                TokenKind::XxlppType => {
                    self.consume_token();
                    Some(DataType::Xxlpp)
                }
                TokenKind::FiberType => {
                    self.consume_token();
                    Some(DataType::Fiber)
                }
                TokenKind::BoobaType => {
                    self.consume_token();
                    Some(DataType::Booba)
                }
                TokenKind::Identifier => {
                    let name = self.match_token(TokenKind::Identifier);
                    Some(DataType::Struct { name })
                }
                _ => {
                    self.consume_token();
                    None
                }
            };
        }
        None
    }

    fn _struct_(&mut self) -> DataType {
        todo!()
    }

    fn expression(&mut self) -> Option<Expression> {
        self.equality()
    }

    fn equality(&mut self) -> Option<Expression> {
        let position = self.position;
        let mut comparison = self.comparison();

        while self.matches_token_kind(TokenKind::BangEqual)
            || self.matches_token_kind(TokenKind::EqualEqual)
        {
            let op = self.binop(|kind| match kind {
                TokenKind::BangEqual => BinaryOperator::NotEqual,
                TokenKind::EqualEqual => BinaryOperator::Equal,
                _ => unreachable!(),
            });

            let rhs = self.match_(Self::comparison, "expression");
            comparison.as_ref()?;
            if let Some(expression) = comparison {
                comparison = Some(Expression::BinaryExpression {
                    position,
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }

        comparison
    }

    fn comparison(&mut self) -> Option<Expression> {
        let position = self.position;
        let mut term = self.term();

        while self.matches_token_kind(TokenKind::Greater)
            || self.matches_token_kind(TokenKind::GreaterEqual)
            || self.matches_token_kind(TokenKind::Less)
            || self.matches_token_kind(TokenKind::LessEqual)
        {
            let op = self.binop(|kind| match kind {
                TokenKind::Greater => BinaryOperator::GreaterThan,
                TokenKind::GreaterEqual => BinaryOperator::GreaterThanOrEqual,
                TokenKind::Less => BinaryOperator::LessThan,
                TokenKind::LessEqual => BinaryOperator::LessThanOrEqual,
                _ => unreachable!(),
            });
            let rhs = self.match_(Self::term, "expression");
            if term.is_none() {
                self.add_error("expression");
            }

            let expression = term?;
            term = Some(Expression::BinaryExpression {
                position,
                lhs: Box::new(expression),
                op,
                rhs: Box::new(rhs),
            });
        }

        term
    }

    fn term(&mut self) -> Option<Expression> {
        let position = self.position;
        let mut factor = self.factor();

        while self.matches_token_kind(TokenKind::Dash) || self.matches_token_kind(TokenKind::Plus) {
            let op = self.binop(|kind| match kind {
                TokenKind::Dash => BinaryOperator::Subtract,
                TokenKind::Plus => BinaryOperator::Add,
                _ => unreachable!(),
            });
            let rhs = self.match_(Self::factor, "expression");
            factor.as_ref()?;

            if let Some(expression) = factor {
                factor = Some(Expression::BinaryExpression {
                    position,
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }

        factor
    }

    fn factor(&mut self) -> Option<Expression> {
        let position = self.position;
        let mut unary = self.unary();

        while self.matches_token_kind(TokenKind::ForwardSlash)
            || self.matches_token_kind(TokenKind::Star)
        {
            let op = self.binop(|kind| match kind {
                TokenKind::ForwardSlash => BinaryOperator::Divide,
                TokenKind::Star => BinaryOperator::Multiply,
                _ => unreachable!(),
            });
            unary.as_ref()?;
            if let Some(expression) = unary {
                let rhs = self.match_(Self::unary, "expression");
                unary = Some(Expression::BinaryExpression {
                    position,
                    lhs: Box::new(expression),
                    op,
                    rhs: Box::new(rhs),
                });
            }
        }
        unary
    }

    fn unary(&mut self) -> Option<Expression> {
        let position = self.position;
        if self.matches_token_kind(TokenKind::Bang) || self.matches_token_kind(TokenKind::Dash) {
            let op = self.unop(|kind| match kind {
                TokenKind::Bang => UnaryOperator::Not,
                TokenKind::Dash => UnaryOperator::Negate,
                _ => unreachable!(),
            });
            let operand = self.match_(Self::unary, "expression");
            return Some(Expression::UnaryExpression {
                position,
                op,
                operand: Box::new(operand),
            });
        }

        self.primary()
    }

    fn primary(&mut self) -> Option<Expression> {
        let position = self.position;
        if let Some(identifier) = self.match_token_maybe(TokenKind::Identifier) {
            return if self.match_token_maybe(TokenKind::OpenParen).is_some() {
                let arguments = self.match_(Self::arguments, "arguments");
                self.match_token(TokenKind::CloseParen);

                return Some(Expression::FunctionCall {
                    position,
                    identifier,
                    arguments,
                });
            } else if self.match_token_maybe(TokenKind::Equal).is_some() {
                let expression = self.match_(Self::expression, "expression");
                Some(Expression::AssignmentExpression {
                    position,
                    identifier,
                    expression: Box::new(expression),
                })
            } else {
                Some(Expression::IdentifierExpression {
                    position,
                    identifier,
                })
            };
        } else if self.match_token_maybe(TokenKind::NomKeyword).is_some() {
            return Some(Expression::BoobaExpression {
                position,
                booba: false,
            });
        } else if self.match_token_maybe(TokenKind::YemKeyword).is_some() {
            return Some(Expression::BoobaExpression {
                position,
                booba: true,
            });
        } else if let Some(number) = self.match_token_maybe(TokenKind::Number) {
            return Some(Expression::PpExpression {
                position,
                pp: number.parse::<i32>().unwrap(),
            });
        } else if let Some(fiber) = self.match_token_maybe(TokenKind::FiberType) {
            return Some(Expression::FiberExpression { position, fiber });
        } else if self.match_token_maybe(TokenKind::OpenParen).is_some() {
            let expression = self.match_(Self::expression, "expression");
            self.match_token(TokenKind::CloseParen);
            return Some(expression);
        }

        None
    }

    fn arguments(&mut self) -> Option<Vec<Expression>> {
        let mut args = Vec::<Expression>::new();
        // No expressions provided, just return an empty vec. Don't consume the close
        // parenthesis as the caller does that for us.
        if self.matches_token_kind(TokenKind::CloseParen) {
            return Some(args);
        }

        loop {
            let expression = self.is_word(Self::expression)?;
            args.push(expression);
            if self.match_token_maybe(TokenKind::Comma).is_none() {
                break;
            }
        }

        Some(args)
    }

    fn matches_token_kind(&mut self, token_kind: TokenKind) -> bool {
        if let Some(token) = self.token() {
            return token.kind() == token_kind;
        }
        false
    }

    fn match_token_with_result_maybe<T: Default>(
        &mut self,
        token_kind: TokenKind,
    ) -> Result<String, T> {
        if let Some(token) = self.token() {
            if token.kind() == token_kind {
                let optional_token_value = token.value();
                self.consume_token();
                if let Some(token_value) = optional_token_value {
                    return Ok(token_value);
                }
                return Ok(String::new());
            }
        }

        Err(T::default())
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

    fn is_word<T: Default + Eq>(&mut self, grammar_func: fn(&mut Self) -> Option<T>) -> Option<T> {
        if let Some(ret_from_something) = grammar_func(self) {
            return Some(ret_from_something);
        }

        None
    }

    fn match_<T: Default>(
        &mut self,
        grammar_func: fn(&mut Self) -> Option<T>,
        error_message: &str,
    ) -> T {
        if let Some(ret_from_something) = grammar_func(self) {
            return ret_from_something;
        }

        self.add_error(error_message);
        T::default()
    }

    fn add_error(&mut self, error_message: &str) {
        self.error_diag
            .borrow_mut()
            .expected_something_error(error_message, self.token_offset(-1));
    }
}
