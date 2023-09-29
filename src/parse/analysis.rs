use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::evaluate::{BoundExpression, Evaluator};
use crate::parse::parser::{DataType, Function, Statement, TranslationUnit};

pub struct SemanticAnalyzer {
    scopes: Vec<HashMap<String, BoundVariable>>,
    function_scopes: Vec<BoundFunction>,
    error_diag: Arc<RefCell<ErrorDiagnosis>>,
    evaluator: Evaluator,
}

#[derive(Debug)]
pub struct BoundFunction {
    name: String,
    return_type: DataType,
}

#[derive(Debug)]
pub struct BoundVariable {
    identifier: String,
    data_type: DataType,
    value: Option<BoundExpression>,
    initialized: bool,
}

#[derive(Debug)]
pub struct BoundParameter {
    pub identifier: String,
    pub data_type: DataType,
}

pub struct BoundTranslationUnit {}

impl SemanticAnalyzer {
    pub fn new(error_diag: Arc<RefCell<ErrorDiagnosis>>) -> Self {
        Self {
            scopes: Vec::default(),
            function_scopes: Vec::default(),
            error_diag,
            evaluator: Evaluator,
        }
    }

    pub fn build_sym_table(&mut self, translation_unit: TranslationUnit) -> BoundTranslationUnit {
        BoundTranslationUnit {}
    }

    pub fn analyze(&mut self, translation_unit: TranslationUnit) {
        let functions = translation_unit.functions;
        let variables = translation_unit.variables;

        self.begin_scope();
        {
            for variable in variables {
                self.handle_statement(variable);
            }

            for function in functions {
                self.begin_function(&function);
                {
                    for statement in function.block.statements {
                        self.handle_statement(statement);
                    }
                }
                self.end_function();
            }
        }
        self.end_scope();
    }

    fn begin_function(&mut self, function: &Function) {
        let mut params = Vec::new();
        for parameter in &function.parameters {
            params.push(BoundParameter {
                identifier: parameter.identifier.clone(),
                data_type: parameter.data_type.clone(),
            })
        }

        self.function_scopes.push(BoundFunction {
            name: function.identifier.clone(),
            return_type: function.return_type.clone(),
        });
        self.begin_scope();
    }
    fn end_function(&mut self) {
        self.end_scope();
    }

    fn scope_mut(&mut self) -> &mut HashMap<String, BoundVariable> {
        self.scopes.last_mut().expect("A scope")
    }

    fn scope(&self) -> &HashMap<String, BoundVariable> {
        self.scopes.last().expect("A scope")
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop().expect("A scope to pop");
    }

    fn get_variable(&self, identifier: &str) -> Option<&BoundVariable> {
        for scope in &self.scopes {
            if let Some(bound_variable) = scope.get(identifier) {
                return Some(bound_variable);
            }
        }
        None
    }

    fn handle_statement(&mut self, statement: Statement) {
        match statement {
            Statement::VariableDeclaration { variable } => {
                if self.scope().contains_key(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier.as_str(),
                    );
                }

                let scope = self.scope_mut();
                let ident = variable.identifier.clone();
                let bound_var = BoundVariable {
                    identifier: variable.identifier.clone(),
                    value: None,
                    initialized: false,
                    data_type: variable.data_type.clone(),
                };
                dbg!(&bound_var);
                scope.insert(ident, bound_var);
            }
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                if let Some(_) = self.scope().get(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier.as_str(),
                    );
                    return;
                }

                let expr = self.evaluator.evaluate_expr(&expression);
                let same_data_type = match &expr {
                    BoundExpression::PpValue(_) => variable.data_type == DataType::Pp,
                    BoundExpression::BoobaValue(_) => variable.data_type == DataType::Booba,
                    BoundExpression::YarnValue(_) => variable.data_type == DataType::Yarn,
                    BoundExpression::IdentifierValue(identifier) => {
                        let bound_variable = self.get_variable(identifier).unwrap();
                        bound_variable.data_type == variable.data_type
                    }
                    BoundExpression::EmptyValue => {
                        panic!()
                    }
                };

                if !same_data_type {
                    self.error_diag.borrow_mut().invalid_type(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier.as_str(),
                    );
                }

                if !self.scope_mut().contains_key(&variable.identifier) {
                    let ident = variable.identifier.clone();
                    let bound_var = BoundVariable {
                        identifier: variable.identifier.clone(),
                        data_type: variable.data_type.clone(),
                        value: Some(expr),
                        initialized: true,
                    };
                    self.scope_mut().insert(ident, bound_var);
                } else {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier.as_str(),
                    );
                }
            }
            Statement::PprintStatement { expression, .. } => {
                // TODO: Clean this up.
                let expr = self.evaluator.evaluate_expr(&expression);
                if let BoundExpression::YarnValue(yarn_expr) = expr {
                    print!("{}", yarn_expr);
                } else if let BoundExpression::IdentifierValue(identifier) = expr {
                    if let Some(variable) = self.get_variable(&identifier) {
                        if !&variable.initialized {
                            panic!("Variable \"{identifier}\" not yet initialized")
                        }
                        let expression = &variable
                            .value
                            .as_ref()
                            .expect("Initialized variable has no value");
                        if let BoundExpression::YarnValue(yarn_expr) = expression {
                            print!("{}", yarn_expr);
                        } else if let BoundExpression::PpValue(pp_val) = expression {
                            print!("{}", pp_val);
                        } else {
                            panic!("Invalid type for pprint statement")
                        }
                    } else {
                        panic!("Variable \"{identifier}\" does not exist")
                    }
                } else {
                    panic!("Invalid type for pprint statement")
                }
            }
            Statement::ByeStatement { expression, .. } => {
                let expr = self.evaluator.evaluate_expr(&expression);
                if let BoundExpression::IdentifierValue(identifier) = expr {
                    if let Some(variable) = self.get_variable(&identifier) {
                        if !&variable.initialized {
                            panic!("Variable \"{identifier}\" not yet initialized")
                        }
                        let expr = &variable
                            .value
                            .as_ref()
                            .expect("Initialized variable has no value");

                        let same_data_type = match &expr {
                            BoundExpression::PpValue(_) => variable.data_type == DataType::Pp,
                            BoundExpression::BoobaValue(_) => variable.data_type == DataType::Booba,
                            BoundExpression::YarnValue(_) => variable.data_type == DataType::Yarn,
                            BoundExpression::IdentifierValue(identifier) => {
                                let bound_variable = self.get_variable(identifier).unwrap();
                                bound_variable.data_type == variable.data_type
                            }
                            BoundExpression::EmptyValue => {
                                panic!()
                            }
                        };
                    }
                }
            }
            _ => {}
        }
    }
}
