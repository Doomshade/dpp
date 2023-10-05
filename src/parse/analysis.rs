use crate::emit::emitter::{Emitter, Instruction};
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::marker::PhantomData;
use std::rc::Rc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::evaluate::{BoundExpression, Evaluator};
use crate::parse::parser::{DataType, Expression, Function, Statement, TranslationUnit};

pub struct SemanticAnalyzer<'a, 'b, T>
where
    T: Write,
{
    scopes: Vec<HashMap<&'a str, BoundVariable<'a>>>,
    function_scopes: Vec<BoundFunction<'a>>,
    error_diag: Rc<RefCell<ErrorDiagnosis<'a, 'b>>>,
    evaluator: Evaluator<'a>,
    emitter: Emitter<T>,
}

#[derive(Clone, Debug)]
pub struct BoundFunction<'a> {
    name: &'a str,
    return_type: DataType<'a>,
}

#[derive(Clone, Debug)]
pub struct BoundVariable<'a> {
    position: (u32, u32),
    identifier: &'a str,
    data_type: DataType<'a>,
    value: Option<Expression<'a>>,
    initialized: bool,
}

#[derive(Debug)]
pub struct BoundParameter<'a> {
    pub identifier: &'a str,
    pub data_type: DataType<'a>,
}

impl<'a, 'b, T: Write> SemanticAnalyzer<'a, 'b, T> {
    pub fn new(error_diag: Rc<RefCell<ErrorDiagnosis<'a, 'b>>>, emitter: Emitter<T>) -> Self {
        Self {
            scopes: Vec::default(),
            function_scopes: Vec::default(),
            error_diag,
            evaluator: Evaluator { none: PhantomData },
            emitter,
        }
    }

    fn statement_to_variable(&self, statement: &Statement<'a>) -> Option<&BoundVariable<'a>> {
        return match statement {
            Statement::VariableDeclaration { variable } => self.get_variable(variable.identifier),
            Statement::VariableDeclarationAndAssignment { variable, .. } => {
                self.get_variable(variable.identifier)
            }
            _ => {
                panic!("Invalid statement type")
            }
        };
    }

    fn begin_global_scope(&mut self, translation_unit: &TranslationUnit<'a>) {
        self.begin_scope();
        let functions = &translation_unit.functions;
        let statements = &translation_unit.global_statements;

        for statement in statements {
            if let Some(variable) = self.statement_to_variable(statement) {
                let identifier = variable.identifier;
                if self.scope().contains_key(&identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        identifier,
                    );
                }

                let bound_var = BoundVariable {
                    position: variable.position,
                    identifier,
                    value: None,
                    initialized: false,
                    data_type: variable.data_type.clone(),
                };
                dbg!(&bound_var);
                let scope = self.scope_mut();
                scope.insert(identifier, bound_var);
            }
        }

        for function in functions {
            if self.scope().contains_key(&function.identifier) {
                self.error_diag.borrow_mut().function_already_exists(
                    function.position.0,
                    function.position.1,
                    function.identifier,
                );
            }

            let scope = self.scope_mut();
            let bound_var = BoundVariable {
                position: function.position,
                identifier: function.identifier,
                value: None,
                initialized: false,
                data_type: function.return_type.clone(),
            };
            dbg!(&bound_var);
            scope.insert(function.identifier, bound_var);
        }
    }

    fn end_global_scope(&mut self) {
        self.end_scope();
    }

    pub fn analyze(&mut self, translation_unit: TranslationUnit<'a>) {
        self.begin_global_scope(&translation_unit);
        {
            // Analyze global statements and functions.
            for statement in translation_unit.global_statements {
                self.handle_global_statement(statement);
            }

            for function in translation_unit.functions {
                self.begin_function(&function);
                {
                    for statement in function.block.statements {
                        self.handle_statement(statement);
                    }
                }
                self.end_function();
            }
        }
        self.end_global_scope();
        self.emitter
            .emit_instruction(Instruction::JMP { address: 0 })
            .expect("asd");
    }

    fn begin_function(&mut self, function: &Function<'a>) {
        let mut params = Vec::new();
        for parameter in &function.parameters {
            params.push(BoundParameter {
                identifier: parameter.identifier.clone(),
                data_type: parameter.data_type.clone(),
            });
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

    fn scope_mut(&mut self) -> &mut HashMap<&'a str, BoundVariable<'a>> {
        self.scopes.last_mut().expect("A scope")
    }

    fn scope(&self) -> &HashMap<&'a str, BoundVariable<'a>> {
        self.scopes.last().expect("A scope")
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop().expect("A scope to pop");
    }

    fn get_variable(&self, identifier: &str) -> Option<&BoundVariable<'a>> {
        for scope in &self.scopes {
            if let Some(bound_variable) = scope.get(identifier) {
                return Some(bound_variable);
            }
        }
        None
    }

    fn handle_global_statement(&mut self, statement: Statement<'a>) {
        // TODO: Handle only a number of statements.
        self.handle_statement(statement);
    }

    fn handle_statement(&mut self, statement: Statement<'a>) {
        match statement {
            Statement::VariableDeclaration { variable } => {
                if self.scope().contains_key(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }

                let scope = self.scope_mut();
                let bound_var = BoundVariable {
                    position: variable.position,
                    identifier: variable.identifier,
                    value: None,
                    initialized: false,
                    data_type: variable.data_type,
                };
                dbg!(&bound_var);
                scope.insert(variable.identifier, bound_var);
            }
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                if self.scope().get(&variable.identifier).is_some() {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                    return;
                }

                if self.evaluator.eval(&expression) != variable.data_type {
                    self.error_diag.borrow_mut().invalid_type(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }
                dbg!(&expression);

                if self.scope_mut().contains_key(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                } else {
                    self.emitter.emit_expression(&expression).expect("asd");
                    let ident = variable.identifier.clone();
                    let bound_var = BoundVariable {
                        position: variable.position,
                        identifier: variable.identifier.clone(),
                        data_type: variable.data_type.clone(),
                        value: Some(expression),
                        initialized: true,
                    };
                    self.scope_mut().insert(ident, bound_var);
                }
            }
            Statement::PrintStatement {
                expression,
                print_function,
                ..
            } => {}
            Statement::ByeStatement { expression, .. } => {}
            _ => {}
        }
    }
}
