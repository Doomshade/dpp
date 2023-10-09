use std::marker::PhantomData;

use crate::parse::parser::{DataType, Expression, UnaryOperator};

pub struct Evaluator<'a> {
    pub none: PhantomData<&'a ()>,
}

impl<'a> Evaluator<'a> {}
