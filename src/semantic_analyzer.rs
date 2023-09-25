use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parser::{Block, DataType, Expression, Function, Statement, TranslationUnit};

pub struct SemanticAnalyzer {
    symbol_table: Vec<HashMap<String, DataType>>,
    globals: HashMap<String, DataType>,
    error_diag: Arc<RefCell<ErrorDiagnosis>>,
}

impl SemanticAnalyzer {
    pub fn new(error_diag: Arc<RefCell<ErrorDiagnosis>>) -> Self {
        Self {
            symbol_table: Vec::default(),
            globals: HashMap::default(),
            error_diag,
        }
    }

    pub fn analyze(&mut self, translation_unit: TranslationUnit) {
        match translation_unit {
            TranslationUnit::TranslationUnit {
                functions,
                variables,
            } => {
                for variable in variables {
                    self.handle_statement(variable);
                }

                for function in functions {
                    match function {
                        Function::Function {
                            identifier,
                            return_type,
                            position,
                            block,
                            ..
                        } => {
                            if self.globals.contains_key(&identifier) {
                                self.error_diag.borrow_mut().variable_already_exists(
                                    position.0,
                                    position.1,
                                    identifier.as_str(),
                                );
                            } else {
                                self.globals.insert(identifier, return_type);
                            }

                            match block {
                                Block::Block { statements, .. } => {
                                    for statement in statements {
                                        self.handle_statement(statement);
                                    }
                                }
                                Block::InvalidBlock => panic!("RIP"),
                            }
                        }
                        Function::InvalidFunction => panic!("RIP"),
                    }
                }
            }
            TranslationUnit::InvalidTranslationUnit => panic!("RIP"),
        };
    }

    ///
    ///
    /// # Arguments
    ///
    /// * `block`:
    ///
    /// returns: ()
    ///
    /// # Examples
    ///
    /// ```
    ///
    /// ```
    fn handle_scope(&mut self, block: &Block) {
        match block {
            Block::Block { .. } => {
                let scope = HashMap::new();
                self.symbol_table.push(scope);
            }
            Block::InvalidBlock => {}
        }
    }

    fn handle_statement(&mut self, variable: Statement) {
        match variable {
            Statement::VariableDeclaration {
                identifier,
                data_type,
                position,
            } => {
                for scope in &self.symbol_table {
                    if scope.get(&identifier).is_some() {
                        self.error_diag.borrow_mut().variable_already_exists(
                            position.0,
                            position.1,
                            identifier.as_str(),
                        );
                    }
                }
                if self.globals.contains_key(&identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        position.0,
                        position.1,
                        identifier.as_str(),
                    );
                } else {
                    self.globals.insert(identifier, data_type);
                }
            }
            Statement::VariableDeclarationAndAssignment {
                identifier,
                data_type,
                expression,
                position,
            } => {
                let evaluated_data_type = self.evaluate_expression_data_type(&expression);
                if evaluated_data_type != &data_type {
                    self.error_diag.borrow_mut().invalid_type(
                        position.0,
                        position.1,
                        identifier.as_str(),
                    );
                }
                if !self.globals.contains_key(&identifier) {
                    self.globals.insert(identifier, data_type);
                } else {
                    self.error_diag.borrow_mut().variable_already_exists(
                        position.0,
                        position.1,
                        identifier.as_str(),
                    );
                }
            }
            _ => {}
        }
    }

    fn evaluate_expression_data_type(&self, expression: &Expression) -> &DataType {
        match expression {
            Expression::PpExpression { .. } => &DataType::Pp,
            Expression::BoobaExpression { .. } => &DataType::Booba,
            Expression::FiberExpression { .. } => &DataType::Yarn,
            Expression::UnaryExpression { operand, .. } => {
                self.evaluate_expression_data_type(operand)
            }
            Expression::BinaryExpression { lhs, rhs, .. } => {
                let left_type = self.evaluate_expression_data_type(lhs);
                let right_type = self.evaluate_expression_data_type(rhs);
                assert!(!(left_type != right_type), "invalid binop");

                left_type
            }
            Expression::IdentifierExpression { identifier, .. }
            | Expression::FunctionCall { identifier, .. } => {
                if let Some(data_type) = self.globals.get(identifier) {
                    return data_type;
                }
                for symbols in &self.symbol_table {
                    if let Some(data_type) = symbols.get(identifier) {
                        return data_type;
                    }
                }
                panic!("Unknown identifier {identifier}")
            }
            Expression::AssignmentExpression { identifier, .. } => {
                if let Some(data_type) = self.globals.get(identifier) {
                    return data_type;
                }
                for symbols in &self.symbol_table {
                    if let Some(data_type) = symbols.get(identifier) {
                        return data_type;
                    }
                }
                panic!("Unknown identifier")
            }
            Expression::InvalidExpression => &DataType::InvalidDataType,
        }
    }
}
