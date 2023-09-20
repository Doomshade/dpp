use crate::lexer::{Lexer, Token, TokenKind};

#[derive(Default)]
pub struct Parser;

#[derive(Debug)]
pub enum Statement {
    VariableDeclaration(BoundVariableDeclaration),
}

#[derive(Debug)]
pub struct BoundVariableDeclaration {
    identifier: String,
    _type: DataType,
    expression: Expression,
}

impl BoundVariableDeclaration {
    pub fn identifier(&self) -> &str {
        &self.identifier
    }
    pub fn _type(&self) -> &DataType {
        &self._type
    }
    pub fn expression(&self) -> &Expression {
        &self.expression
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
    pub fn parse(&self, lexer: &mut Lexer) -> Statement {
        lexer.reset();
        lexer.lex().expect("LUL");
        self.statement(lexer)
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

    fn statement(&self, lexer: &mut Lexer) -> Statement {
        if self.matches_token_kind(lexer, TokenKind::LetKeyword) {
            lexer.consume_token();
            if !self.matches_token_kind(lexer, TokenKind::Identifier) {
                panic!("Expected identifier")
            }

            if let None = lexer.token() {
                panic!("Expected identifier")
            }

            let ident = lexer.token().unwrap();
            let identifier = ident.value.as_ref().unwrap().to_string();
            lexer.consume_token();

            if !self.matches_token_kind(lexer, TokenKind::Colon) {
                panic!("Expected \":\"")
            }
            lexer.consume_token();

            let data_type = self.data_type(lexer);

            if !self.matches_token_kind(lexer, TokenKind::Equal) {
                panic!("Expected \"=\"")
            }
            lexer.consume_token();
            let expression = self.expression(lexer);

            if !self.matches_token_kind(lexer, TokenKind::Semicolon) {
                panic!("Expected \";\"")
            }
            lexer.consume_token();

            return Statement::VariableDeclaration(BoundVariableDeclaration {
                identifier: identifier,
                _type: data_type,
                expression,
            });
        }

        panic!("Not a statement")
    }

    fn data_type(&self, lexer: &mut Lexer) -> DataType {
        if let Some(token) = lexer.token() {
            return match token.kind {
                TokenKind::PpType => {
                    lexer.consume_token();
                    DataType::Pp
                }
                _ => self.struct_(lexer),
            };
        }
        panic!("No token")
    }

    fn struct_(&self, lexer: &mut Lexer) -> DataType {
        todo!()
    }

    fn expression(&self, lexer: &mut Lexer) -> Expression {
        self.equality(lexer)
    }

    fn equality(&self, lexer: &mut Lexer) -> Expression {
        let mut expression = self.comparison(lexer);

        while self.matches_token_kind(lexer, TokenKind::BangEqual)
            || self.matches_token_kind(lexer, TokenKind::EqualEqual)
        {
            expression = Expression::BinaryExpression(BoundBinaryExpression {
                lhs: Box::new(expression),
                op: self.op(lexer, |kind| match kind {
                    TokenKind::BangEqual => Op::NotEqual,
                    TokenKind::EqualEqual => Op::Equal,
                    _ => unreachable!(),
                }),
                rhs: Box::new(self.comparison(lexer)),
            });
        }
        expression
    }

    fn comparison(&self, lexer: &mut Lexer) -> Expression {
        let mut expression = self.term(lexer);

        while self.matches_token_kind(lexer, TokenKind::Greater)
            || self.matches_token_kind(lexer, TokenKind::GreaterEqual)
            || self.matches_token_kind(lexer, TokenKind::Less)
            || self.matches_token_kind(lexer, TokenKind::LessEqual)
        {
            expression = Expression::BinaryExpression(BoundBinaryExpression {
                lhs: Box::new(expression),
                op: self.op(lexer, |kind| match kind {
                    TokenKind::Greater => Op::GreaterThan,
                    TokenKind::GreaterEqual => Op::GreaterThanOrEqual,
                    TokenKind::Less => Op::LessThan,
                    TokenKind::LessEqual => Op::LessThanOrEqual,
                    _ => unreachable!(),
                }),
                rhs: Box::new(self.term(lexer)),
            });
        }
        expression
    }

    fn term(&self, lexer: &mut Lexer) -> Expression {
        let mut expression = self.factor(lexer);

        while self.matches_token_kind(lexer, TokenKind::Dash)
            || self.matches_token_kind(lexer, TokenKind::Plus)
        {
            expression = Expression::BinaryExpression(BoundBinaryExpression {
                lhs: Box::new(expression),
                op: self.op(lexer, |kind| match kind {
                    TokenKind::Dash => Op::Subtract,
                    TokenKind::Plus => Op::Add,
                    _ => unreachable!(),
                }),
                rhs: Box::new(self.factor(lexer)),
            });
        }

        expression
    }

    fn factor(&self, lexer: &mut Lexer) -> Expression {
        let mut expression = self.unary(lexer);

        while self.matches_token_kind(lexer, TokenKind::ForwardSlash)
            || self.matches_token_kind(lexer, TokenKind::Star)
        {
            expression = Expression::BinaryExpression(BoundBinaryExpression {
                lhs: Box::new(expression),
                op: self.op(lexer, |kind| match kind {
                    TokenKind::ForwardSlash => Op::Divide,
                    TokenKind::Star => Op::Multiply,
                    _ => unreachable!(),
                }),
                rhs: Box::new(self.unary(lexer)),
            });
        }
        expression
    }

    fn unary(&self, lexer: &mut Lexer) -> Expression {
        if self.matches_token_kind(lexer, TokenKind::Bang)
            || self.matches_token_kind(lexer, TokenKind::Dash)
        {
            return Expression::UnaryExpression(BoundUnaryExpression {
                op: self.op(lexer, |kind| match kind {
                    TokenKind::Bang => Op::Not,
                    TokenKind::Dash => Op::Negate,
                    _ => unreachable!(),
                }),
                operand: Box::new(self.unary(lexer)),
            });
        }

        self.primary(lexer)
    }

    fn primary(&self, lexer: &mut Lexer) -> Expression {
        if self.matches_token_kind(lexer, TokenKind::False) {
            let expression = Expression::BoobaExpression(BoundBoobaExpression { booba: false });
            lexer.consume_token();
            return expression;
        }
        if self.matches_token_kind(lexer, TokenKind::True) {
            let expression = Expression::BoobaExpression(BoundBoobaExpression { booba: true });
            lexer.consume_token();
            return expression;
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
            return expression;
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
            return expression;
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

        unreachable!("Not implemented: {:#?}", lexer.token());
    }

    fn matches_token_kind(&self, lexer: &Lexer, token_kind: TokenKind) -> bool {
        if let Some(token) = lexer.token() {
            return token.kind == token_kind;
        }
        false
    }
}
