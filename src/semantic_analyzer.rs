use crate::parser::TranslationUnit;

pub struct SemanticAnalyzer {
    translation_unit: TranslationUnit,
}

impl SemanticAnalyzer {
    #[must_use] pub fn new(translation_unit: TranslationUnit) -> Self {
        Self { translation_unit }
    }

    pub fn analyze(&mut self) -> &TranslationUnit {
        &self.translation_unit
    }
}
