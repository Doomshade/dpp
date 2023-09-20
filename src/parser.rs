use crate::lexer::{Lexer, TokenKind};

#[derive(Default)]
pub struct Parser;

#[derive(Debug)]
pub enum Statement {
    VariableDeclaration(BoundVariableDeclaration),
    VariableInitialization(BoundVariableInitialization),
    VariableDeclarationAndInitialization(BoundVariableDeclarationAndInitialization),
}

#[derive(Debug)]
pub enum Block {
    Statement(Statement),
    Statements(Vec<Statement>),
}

#[derive(Debug)]
pub struct BoundVariableInitialization {
    identifier: String,
    expression: Expression,
}

impl BoundVariableInitialization {
    pub fn identifier(&self) -> &str {
        &self.identifier
    }
    pub fn expression(&self) -> &Expression {
        &self.expression
    }
}

#[derive(Debug)]
pub struct BoundVariableDeclarationAndInitialization {
    identifier: String,
    data_type: DataType,
    expression: Expression,
}

impl BoundVariableDeclarationAndInitialization {
    pub fn identifier(&self) -> &str {
        &self.identifier
    }
    pub fn data_type(&self) -> &DataType {
        &self.data_type
    }
    pub fn expression(&self) -> &Expression {
        &self.expression
    }
}

#[derive(Debug)]
pub struct BoundVariableDeclaration {
    identifier: String,
    data_type: DataType,
}

impl BoundVariableDeclaration {
    pub fn identifier(&self) -> &str {
        &self.identifier
    }
    pub fn _type(&self) -> &DataType {
        &self.data_type
    }
}

#[derive(Debug)]
pub enum Expression {
    PpExpression(BoundPpExpression),
    BoobaExpression(BoundBoobaExpression),
    FiberExpression(BoundFiberExpression),
    UnaryExpression(BoundUnaryExpression),
    BinaryExpression(BoundBinaryExpression),
}

#[derive(Debug)]
pub enum DataType {
    Pp,
    Struct(Struct),
}

#[derive(Debug)]
pub struct BoundPpDataType {
    pp: i32,
}

#[derive(Debug)]
pub enum Struct {}

#[derive(Debug)]
pub struct Program {}

impl Program {
    #[must_use]
    pub fn expression(&self) -> Option<Expression> {
        todo!()
    }
}

#[derive(Debug)]
pub struct BoundUnaryExpression {
    op: Op,
    operand: Box<Expression>,
}

impl BoundUnaryExpression {
    #[must_use]
    pub const fn op(&self) -> &Op {
        &self.op
    }
    #[must_use]
    pub const fn operand(&self) -> &Box<Expression> {
        &self.operand
    }
}

#[derive(Debug, Default)]
pub struct BoundPpExpression {
    pp: i32,
}

impl BoundPpExpression {
    #[must_use]
    pub const fn pp(&self) -> i32 {
        self.pp
    }
}

#[derive(Debug)]
pub struct BoundFiberExpression {
    fiber: String,
}

impl BoundFiberExpression {
    #[must_use]
    pub const fn fiber(&self) -> &String {
        &self.fiber
    }
}

#[derive(Debug)]
pub struct BoundBoobaExpression {
    booba: bool,
}

impl BoundBoobaExpression {
    #[must_use]
    pub const fn booba(&self) -> bool {
        self.booba
    }
}

#[derive(Debug)]
pub struct BoundBinaryExpression {
    lhs: Box<Expression>,
    op: Op,
    rhs: Box<Expression>,
}

impl BoundBinaryExpression {
    #[must_use]
    pub const fn lhs(&self) -> &Expression {
        &self.lhs
    }

    #[must_use]
    pub const fn op(&self) -> &Op {
        &self.op
    }

    #[must_use]
    pub const fn rhs(&self) -> &Expression {
        &self.rhs
    }
}

// impl fmt::Debug for Program {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         return f
//             .debug_struct("Program")
//             .field("expression", &self.expression)
//             .finish();
//     }
// }

// impl fmt::Debug for Expression {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         let mut debug_struct = f.debug_struct("Expression");
//         if let Some(num) = &self.num {
//             debug_struct.field("num", num);
//         }
//         if let Some(binary_expression) = &self.binary_expression {
//             debug_struct.field("binary_expression", binary_expression);
//         }
//         debug_struct.finish()
//     }
// }

// impl fmt::Debug for BinaryExpression {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         return f
//             .debug_struct("BinaryExpression")
//             .field("lhs", &self.lhs)
//             .field("op", &self.op)
//             .field("rhs", &self.rhs)
//             .finish();
//     }
// }

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
    pub fn parse(&self, lexer: &mut Lexer) -> Block {
        lexer.reset();
        lexer.lex().expect("LUL");
        self.block(lexer).unwrap()
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

    fn block(&self, lexer: &mut Lexer) -> Option<Block> {
        if self.matches_token_kind(lexer, TokenKind::OpenBrace) {
            lexer.consume_token();
            if let Some(statement) = self.statement(lexer) {
                let mut statements = Vec::<Statement>::new();
                statements.push(statement);

                while let Some(statement) = self.statement(lexer) {
                    statements.push(statement);
                }

                if !self.matches_token_kind(lexer, TokenKind::CloseBrace) {
                    panic!("Expected closing brace")
                }
                lexer.consume_token();

                return if statements.len() == 1 {
                    Some(Block::Statement(statements.pop().unwrap()))
                } else {
                    Some(Block::Statements(statements))
                };
            }
        }

        None
    }

    fn statement(&self, lexer: &mut Lexer) -> Option<Statement> {
        if self.matches_token_kind(lexer, TokenKind::LetKeyword) {
            lexer.consume_token();
            if !self.matches_token_kind(lexer, TokenKind::Identifier) {
                panic!("Expected identifier")
            }

            let identifier = lexer.token().unwrap().value.as_ref().unwrap().to_string();
            lexer.consume_token();

            if !self.matches_token_kind(lexer, TokenKind::Colon) {
                panic!("Expected \":\"")
            }
            lexer.consume_token();

            if let Some(data_type) = self.data_type(lexer) {
                if self.matches_token_kind(lexer, TokenKind::Equal) {
                    lexer.consume_token();
                    if let Some(expression) = self.expression(lexer) {
                        if !self.matches_token_kind(lexer, TokenKind::Semicolon) {
                            panic!("Expected \";\"")
                        }
                        lexer.consume_token();

                        return Some(Statement::VariableDeclarationAndInitialization(
                            BoundVariableDeclarationAndInitialization {
                                identifier,
                                data_type,
                                expression,
                            },
                        ));
                    }
                } else if self.matches_token_kind(lexer, TokenKind::Semicolon) {
                    lexer.consume_token();
                    return Some(Statement::VariableDeclaration(BoundVariableDeclaration {
                        identifier,
                        data_type,
                    }));
                } else {
                    panic!("Expected \";\"")
                }
            } else {
                panic!("Expected data type")
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

    fn struct_(&self, lexer: &mut Lexer) -> Option<DataType> {
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
            if let Some(_) = expression {
                let op = self.op(lexer, |kind| match kind {
                    TokenKind::BangEqual => Op::NotEqual,
                    TokenKind::EqualEqual => Op::Equal,
                    _ => unreachable!(),
                });
                if let Some(rhs) = self.comparison(lexer) {
                    expression = Some(Expression::BinaryExpression(BoundBinaryExpression {
                        lhs: Box::new(expression.unwrap()),
                        op,
                        rhs: Box::new(rhs),
                    }));
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
            if let Some(_) = expression {
                let op = self.op(lexer, |kind| match kind {
                    TokenKind::Greater => Op::GreaterThan,
                    TokenKind::GreaterEqual => Op::GreaterThanOrEqual,
                    TokenKind::Less => Op::LessThan,
                    TokenKind::LessEqual => Op::LessThanOrEqual,
                    _ => unreachable!(),
                });
                if let Some(rhs) = self.term(lexer) {
                    expression = Some(Expression::BinaryExpression(BoundBinaryExpression {
                        lhs: Box::new(expression.unwrap()),
                        op,
                        rhs: Box::new(rhs),
                    }));
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
            if let Some(_) = expression {
                let op = self.op(lexer, |kind| match kind {
                    TokenKind::Dash => Op::Subtract,
                    TokenKind::Plus => Op::Add,
                    _ => unreachable!(),
                });
                if let Some(factor) = self.factor(lexer) {
                    expression = Some(Expression::BinaryExpression(BoundBinaryExpression {
                        lhs: Box::new(expression.unwrap()),
                        op,
                        rhs: Box::new(factor),
                    }));
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
            if let Some(_) = expression {
                let op = self.op(lexer, |kind| match kind {
                    TokenKind::ForwardSlash => Op::Divide,
                    TokenKind::Star => Op::Multiply,
                    _ => unreachable!(),
                });
                if let Some(unary) = self.unary(lexer) {
                    expression = Some(Expression::BinaryExpression(BoundBinaryExpression {
                        lhs: Box::new(expression.unwrap()),
                        op,
                        rhs: Box::new(unary),
                    }));
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
                return Some(Expression::UnaryExpression(BoundUnaryExpression {
                    op,
                    operand: Box::new(unary),
                }));
            }
        }

        self.primary(lexer)
    }

    fn primary(&self, lexer: &mut Lexer) -> Option<Expression> {
        if self.matches_token_kind(lexer, TokenKind::False) {
            let expression = Expression::BoobaExpression(BoundBoobaExpression { booba: false });
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::True) {
            let expression = Expression::BoobaExpression(BoundBoobaExpression { booba: true });
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::Number) {
            let expression = Expression::PpExpression(BoundPpExpression {
                pp: lexer
                    .token()
                    .unwrap()
                    .value
                    .as_ref()
                    .unwrap()
                    .parse::<i32>()
                    .unwrap(),
            });
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::String) {
            let expression = Expression::FiberExpression(BoundFiberExpression {
                fiber: lexer
                    .token()
                    .unwrap()
                    .value
                    .as_ref()
                    .unwrap()
                    .parse()
                    .unwrap(),
            });
            lexer.consume_token();
            return Some(expression);
        }
        if self.matches_token_kind(lexer, TokenKind::OpenParen) {
            lexer.consume_token();
            let expression = self.expression(lexer);
            if !self.matches_token_kind(lexer, TokenKind::CloseParen) {
                panic!("Expected closing parenthesis");
            }
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
