use crate::lexer::{Lexer, TokenKind};

#[derive(Default)]
pub struct Parser;

#[derive(Debug)]
pub enum Expression {
    PpExpression(BoundPpExpression),
    BoobaExpression(BoundBoobaExpression),
    FiberExpression(BoundFiberExpression),
    UnaryExpression(BoundUnaryExpression),
    BinaryExpression(BoundBinaryExpression),
}

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
    pub const fn op(&self) -> &Op {
        &self.op
    }
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
    pub fn parse(&self, lexer: &mut Lexer) -> Expression {
        lexer.reset();
        lexer.lex().expect("LUL");
        self.expression(lexer)
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

    fn expression(&self, lexer: &mut Lexer) -> Expression {
        let expression = self.equality(lexer);
        println!("Expression!");
        dbg!(&expression);
        expression
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
            println!("Equality!");
            dbg!(&expression);
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
            println!("Comparison!");
            dbg!(&expression);
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
            println!("Addition or subtraction!");
            dbg!(&expression);
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
            println!("Division or multiplication!");
            dbg!(&expression);
        }
        expression
    }

    fn unary(&self, lexer: &mut Lexer) -> Expression {
        if self.matches_token_kind(lexer, TokenKind::Bang)
            || self.matches_token_kind(lexer, TokenKind::Dash)
        {
            let expression = Expression::UnaryExpression(BoundUnaryExpression {
                op: self.op(lexer, |kind| match kind {
                    TokenKind::Bang => Op::Not,
                    TokenKind::Dash => Op::Negate,
                    _ => unreachable!(),
                }),
                operand: Box::new(self.unary(lexer)),
            });
            println!("Unary!");
            dbg!(&expression);
            return expression;
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
            println!("Number!");
            dbg!(&expression);
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
            println!("String!");
            dbg!(&expression);
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
