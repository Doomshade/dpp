use std::cell::RefCell;
use std::fmt::Debug;
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::lexer::{Token, TokenKind};

#[derive(Debug)]
pub struct Parser {
    tokens: Arc<Vec<Token>>,
    error_diag: Arc<RefCell<ErrorDiagnosis>>,
    curr_token_index: usize,
    position: (u32, u32),
}

// For each declaration in grammar we declare an enum and a function that parses that declaration.
//
// Each enum always consists of a default variant, usually prefixed by "Invalid" that allows us to
// continue parsing even though an error occurred. That way we are able to insert a placeholder
// in the AST and continue parsing. This is useful for error recovery.
//
// Each enum also contains a variant for each possible production in the grammar,
// usually defaulting to one variant with the same name (e.g. Function::Function). This adds a
// little bit of boilerplate, but it allows us to easily add new productions to the grammar.
//
// Each enum also derives Debug that lets us print the tree structure of the AST.

#[derive(Debug, Default)]
pub enum TranslationUnit {
    TranslationUnit {
        functions: Vec<Function>,
        variables: Vec<Statement>,
    },
    #[default]
    InvalidTranslationUnit,
}

#[derive(Debug, Default)]
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

#[derive(Debug, Default)]
pub enum Parameters {
    Parameters {
        position: (u32, u32),
        parameters: Vec<Parameter>,
    },
    #[default]
    InvalidParameters,
}

#[derive(Debug, Default)]
pub enum Parameter {
    Parameter {
        position: (u32, u32),
        identifier: String,
        data_type: DataType,
    },
    #[default]
    InvalidParameter,
}

#[derive(Debug, Default)]
pub enum Block {
    Block {
        position: (u32, u32),
        statements: Vec<Statement>,
    },
    #[default]
    InvalidBlock,
}

#[derive(Debug, Default)]
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
    ForStatement {
        position: (u32, u32),
        index_ident: String,
        length_expression: Expression,
        statement: Box<Statement>,
    },
    ForStatementWithIdentExpression {
        position: (u32, u32),
        ident: Expression,
        length_expression: Expression,
        statement: Box<Statement>,
    },
    WhileStatement {
        position: (u32, u32),
        expression: Expression,
        statement: Box<Statement>,
    },
    #[default]
    InvalidStatement,
    DoWhileStatement {
        position: (u32, u32),
        block: Block,
        expression: Expression,
    },
    LoopStatement {
        position: (u32, u32),
        block: Box<Block>,
    },
    BreakStatement {
        position: (u32, u32),
    },
    ContinueStatement {
        position: (u32, u32),
    },
}

#[derive(Debug, Default)]
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

#[derive(Debug, Default, Eq, PartialEq)]
pub enum DataType {
    Xxlpp,
    Nopp,
    Pp,
    Spp,
    Xspp,
    P,
    Yarn,
    Booba,
    Struct {
        name: String,
    },
    #[default]
    InvalidDataType,
}

#[derive(Debug, Default)]
pub enum Struct {
    #[default]
    InvalidStruct,
}

#[derive(Debug, Default)]
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

#[derive(Debug, Default)]
pub enum UnaryOperator {
    Not,
    Negate,
    #[default]
    InvalidUnaryOperator,
}

impl Parser {
    pub fn new(tokens: Arc<Vec<Token>>, error_diag: Arc<RefCell<ErrorDiagnosis>>) -> Self {
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

    fn matches_token_kind(&mut self, token_kind: TokenKind) -> bool {
        if let Some(token) = self.token() {
            return token.kind() == token_kind;
        }
        false
    }

    fn accepts(&mut self, token_kind: TokenKind) -> Option<String> {
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

    fn expect(&mut self, token_kind: TokenKind) -> String {
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

    fn accepts_<T: Default>(&mut self, grammar_func: fn(&mut Self) -> Option<T>) -> Option<T> {
        if let Some(ret_from_something) = grammar_func(self) {
            return Some(ret_from_something);
        }

        None
    }

    fn expect_<T: Default>(
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
            if let Some(function) = self.accepts_(Self::function) {
                functions.push(function);
            } else if let Some(variable_declaration) = self.accepts_(Self::var_decl) {
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
        self.accepts(TokenKind::FUNcKeyword)?;

        let identifier = self.expect(TokenKind::Identifier);
        let parameters = self.params();
        self.expect(TokenKind::Arrow);
        let return_type = self.expect_(Self::data_type, "data type");
        let block = self.expect_(Self::block, "block");

        Some(Function::Function {
            position,
            identifier,
            return_type,
            parameters,
            block,
        })
    }

    fn params(&mut self) -> Vec<Parameter> {
        self.expect(TokenKind::OpenParen);
        let mut parameters = Vec::<Parameter>::new();

        // Check if the close parenthesis is present first,
        // then try to parse a parameter. If a parameter is present,
        // check if "," or the close parenthesis is there.
        // If neither is there, we say we expected
        if self.accepts(TokenKind::CloseParen).is_some() {
            return parameters;
        }

        let parameter = self.parameter();
        parameters.push(parameter);
        loop {
            if self.accepts(TokenKind::Comma).is_some() {
                parameters.push(self.parameter());
            } else if self.accepts(TokenKind::CloseParen).is_some() {
                break;
            } else {
                self.add_error("Expected \",\"");
                parameters.push(self.parameter());
            }
        }

        parameters
    }

    fn parameter(&mut self) -> Parameter {
        let position = self.position;
        let identifier = self.expect(TokenKind::Identifier);
        self.expect(TokenKind::Colon);
        let data_type = self.expect_(Self::data_type, "data type");
        Parameter::Parameter {
            position,
            identifier,
            data_type,
        }
    }

    fn block(&mut self) -> Option<Block> {
        let position = self.position;
        self.accepts(TokenKind::OpenBrace)?;
        let mut statements = Vec::<Statement>::new();
        while let Some(statement) = self.statement() {
            statements.push(statement);
        }
        self.expect(TokenKind::CloseBrace);

        Some(Block::Block {
            position,
            statements,
        })
    }

    fn statement(&mut self) -> Option<Statement> {
        let position = self.position;
        if self.accepts(TokenKind::IfKeyword).is_some() {
            self.expect(TokenKind::OpenParen);
            let expression = self.expect_(Self::expr, "expression");
            self.expect(TokenKind::CloseParen);

            let statement = self.expect_(Self::statement, "statement");
            return if self.accepts(TokenKind::ElseKeyword).is_some() {
                let else_statement = self.expect_(Self::statement, "statement");
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
        } else if self.accepts(TokenKind::ForKeyword).is_some() {
            self.expect(TokenKind::OpenParen);
            let ident = self.expect(TokenKind::Identifier);
            let ident_expression: Option<Expression>;
            if self.accepts(TokenKind::Equal).is_some() {
                ident_expression = Some(self.expect_(Self::expr, "expression"));
            } else {
                ident_expression = None;
            }
            self.expect(TokenKind::ToKeyword);
            let expression = self.expect_(Self::expr, "expression");
            self.expect(TokenKind::CloseParen);
            let statement = self.expect_(Self::statement, "statement");

            if let Some(ident_expression) = ident_expression {
                return Some(Statement::ForStatementWithIdentExpression {
                    position,
                    ident: ident_expression,
                    length_expression: expression,
                    statement: Box::new(statement),
                });
            }

            return Some(Statement::ForStatement {
                position,
                index_ident: ident,
                length_expression: expression,
                statement: Box::new(statement),
            });
        } else if self.accepts(TokenKind::WhileKeyword).is_some() {
            self.expect(TokenKind::OpenParen);
            let expression = self.expect_(Self::expr, "expression");
            self.expect(TokenKind::CloseParen);
            let statement = self.expect_(Self::statement, "statement");

            return Some(Statement::WhileStatement {
                position,
                expression,
                statement: Box::new(statement),
            });
        } else if self.accepts(TokenKind::DoKeyword).is_some() {
            let block = self.expect_(Self::block, "block");
            self.expect(TokenKind::WhileKeyword);
            self.expect(TokenKind::OpenParen);
            let expression = self.expect_(Self::expr, "expression");
            self.expect(TokenKind::CloseParen);
            self.expect(TokenKind::Semicolon);
            return Some(Statement::DoWhileStatement {
                position,
                block,
                expression,
            });
        } else if self.accepts(TokenKind::LoopKeyword).is_some() {
            let block = self.expect_(Self::block, "block");
            return Some(Statement::LoopStatement {
                position,
                block: Box::new(block),
            });
        } else if self.accepts(TokenKind::BreakKeyword).is_some() {
            self.expect(TokenKind::Semicolon);
            return Some(Statement::BreakStatement { position });
        } else if self.accepts(TokenKind::ContinueKeyword).is_some() {
            self.expect(TokenKind::Semicolon);
            return Some(Statement::ContinueStatement { position });
        } else if self.accepts(TokenKind::ByeKeyword).is_some() {
            let expression = self.expect_(Self::expr, "expression");
            self.expect(TokenKind::Semicolon);

            return Some(Statement::ReturnStatement {
                position,
                expression,
            });
        } else if self.accepts(TokenKind::Semicolon).is_some() {
            return Some(Statement::EmptyStatement { position });
        } else if let Some(variable_declaration) = self.var_decl() {
            return Some(variable_declaration);
        } else if let Some(block) = self.block() {
            return Some(Statement::BlockStatement {
                position,
                block: Box::new(block),
            });
        } else if let Some(expression) = self.expr() {
            self.expect(TokenKind::Semicolon);
            return Some(Statement::ExpressionStatement {
                position,
                expression,
            });
        }

        None
    }

    fn var_decl(&mut self) -> Option<Statement> {
        let position = self.position;
        let data_type = self.accepts_(Self::data_type)?;
        self.expect(TokenKind::Arrow);

        let identifier = self.expect(TokenKind::Identifier);
        let statement = if self.accepts(TokenKind::Equal).is_some() {
            let expression = self.expect_(Self::expr, "expression");
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

        self.expect(TokenKind::Semicolon);
        Some(statement)
    }

    fn data_type(&mut self) -> Option<DataType> {
        if let Some(token) = self.token() {
            return match token.kind() {
                TokenKind::XxlppType => {
                    self.consume_token();
                    Some(DataType::Xxlpp)
                }
                TokenKind::PpType => {
                    self.consume_token();
                    Some(DataType::Pp)
                }
                TokenKind::SppType => {
                    self.consume_token();
                    Some(DataType::Spp)
                }
                TokenKind::XsppType => {
                    self.consume_token();
                    Some(DataType::Xspp)
                }
                TokenKind::PType => {
                    self.consume_token();
                    Some(DataType::P)
                }
                TokenKind::NoppType => {
                    self.consume_token();
                    Some(DataType::Nopp)
                }
                TokenKind::BoobaType => {
                    self.consume_token();
                    Some(DataType::Booba)
                }
                TokenKind::YarnType => {
                    self.consume_token();
                    Some(DataType::Yarn)
                }
                _ => None,
            };
        }
        None
    }

    fn _struct_(&mut self) -> DataType {
        todo!()
    }

    fn expr(&mut self) -> Option<Expression> {
        self.equ()
    }

    fn equ(&mut self) -> Option<Expression> {
        let position = self.position;
        let mut comparison = self.comp();

        while self.matches_token_kind(TokenKind::BangEqual)
            || self.matches_token_kind(TokenKind::EqualEqual)
        {
            let op = self.binop(|kind| match kind {
                TokenKind::BangEqual => BinaryOperator::NotEqual,
                TokenKind::EqualEqual => BinaryOperator::Equal,
                _ => unreachable!(),
            });

            let rhs = self.expect_(Self::comp, "expression");
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

    fn comp(&mut self) -> Option<Expression> {
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
            let rhs = self.expect_(Self::term, "expression");
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
            let rhs = self.expect_(Self::factor, "expression");
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
                let rhs = self.expect_(Self::unary, "expression");
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
            let operand = self.expect_(Self::unary, "expression");
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
        if let Some(identifier) = self.accepts(TokenKind::Identifier) {
            return if let Some(arguments) = self.args() {
                return Some(Expression::FunctionCall {
                    position,
                    identifier,
                    arguments,
                });
            } else if self.accepts(TokenKind::Equal).is_some() {
                let expression = self.expect_(Self::expr, "expression");
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
        } else if self.accepts(TokenKind::NomKeyword).is_some() {
            return Some(Expression::BoobaExpression {
                position,
                booba: false,
            });
        } else if self.accepts(TokenKind::YemKeyword).is_some() {
            return Some(Expression::BoobaExpression {
                position,
                booba: true,
            });
        } else if let Some(number) = self.accepts(TokenKind::Number) {
            return Some(Expression::PpExpression {
                position,
                pp: number.parse::<i32>().unwrap(),
            });
        } else if let Some(fiber) = self.accepts(TokenKind::YarnType) {
            return Some(Expression::FiberExpression { position, fiber });
        } else if self.accepts(TokenKind::OpenParen).is_some() {
            let expression = self.expect_(Self::expr, "expression");
            self.expect(TokenKind::CloseParen);
            return Some(expression);
        }

        None
    }

    fn args(&mut self) -> Option<Vec<Expression>> {
        self.accepts(TokenKind::OpenParen)?;
        let mut args = Vec::<Expression>::new();

        if self.accepts(TokenKind::CloseParen).is_some() {
            return Some(args);
        }
        // else if let Some(arg) = self.expr() {
        //     args.push(arg);
        //     loop {
        //         if self.accepts(TokenKind::Comma).is_some() {
        //             args.push(self.expect_(Self::expr, "expression"));
        //         } else if self.accepts(TokenKind::CloseParen).is_some() {
        //             break;
        //         }
        //     }
        // } else {
        //     self.expect(TokenKind::CloseParen);
        // }
        let arg = self.expect_(Self::expr, "expression");
        args.push(arg);
        loop {
            if self.accepts(TokenKind::Comma).is_some() {
                args.push(self.expect_(Self::expr, "expression"));
            } else if self.accepts(TokenKind::CloseParen).is_some() {
                break;
            } else {
                self.add_error("Expected \",\"");
                args.push(self.expect_(Self::expr, "expression"));
            }
        }
        Some(args)
    }
}
