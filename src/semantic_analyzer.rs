use crate::parser::{Parser, TranslationUnit};

pub struct SemanticAnalyzer {
    parser: Parser,
}

impl SemanticAnalyzer {
    pub fn new(parser: Parser) -> Self {
        Self { parser }
    }

    pub fn analyze(&mut self) -> TranslationUnit {
        self.parser.parse()
    }

    pub fn parser(&self) -> &Parser {
        &self.parser
    }
}
