use crate::emit::emitter::{Emitter, Instruction};
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::marker::PhantomData;
use std::rc::Rc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::evaluate::Evaluator;
use crate::parse::parser::{DataType, Expression, Function, Statement, TranslationUnit};

#[derive(Default)]
struct Scope<'a> {
    variables: HashMap<&'a str, BoundVariable<'a>>,
    functions: HashMap<&'a str, BoundFunction<'a>>,
}

impl<'a> Scope<'a> {
    fn push_variable(&mut self, variable: BoundVariable<'a>) {
        self.variables.insert(variable.identifier, variable);
    }
    fn push_function(&mut self, function: BoundFunction<'a>) {
        self.functions.insert(function.identifier, function);
    }

    fn get_variable(&self, identifier: &str) -> Option<&BoundVariable<'a>> {
        self.variables.get(identifier)
    }

    fn get_function(&self, identifier: &str) -> Option<&BoundFunction<'a>> {
        self.functions.get(identifier)
    }

    fn has_variable(&self, identifier: &str) -> bool {
        self.variables.contains_key(identifier)
    }
    fn has_function(&self, identifier: &str) -> bool {
        self.functions.contains_key(identifier)
    }
}

pub struct SemanticAnalyzer<'a, 'b, T>
where
    T: Write,
{
    /// Current stack of scopes. The initial scope is the global scope that should be popped
    /// at the end of the analysis.
    scopes: Vec<Scope<'a>>,
    error_diag: Rc<RefCell<ErrorDiagnosis<'a, 'b>>>,
    evaluator: Evaluator<'a>,
    emitter: Emitter<T>,
}

#[derive(Clone, Debug)]
pub struct BoundFunction<'a> {
    identifier: &'a str,
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
            error_diag,
            evaluator: Evaluator { none: PhantomData },
            emitter,
        }
    }

    pub fn analyze(&mut self, translation_unit: TranslationUnit<'a>) {
        self.begin_global_scope(&translation_unit);
        {
            // Analyze global statements and functions.
            for statement in translation_unit.global_statements {
                self.analyze_global_statement(statement);
            }

            for function in translation_unit.functions {
                self.analyze_function(function);
            }
        }
        self.end_global_scope();
        self.emitter
            .emit_instruction(Instruction::JMP { address: 0 })
            .expect("asd");
    }

    fn analyze_function(&mut self, function: Function<'a>) {
        self.begin_function(&function);
        {
            for statement in function.block.statements {
                self.analyze_statement(statement);
            }
        }
        self.end_function();
    }

    fn analyze_global_statement(&mut self, statement: Statement<'a>) {
        // TODO: Handle only a number of statements.
        self.analyze_statement(statement);
    }

    fn analyze_statement(&mut self, statement: Statement<'a>) {
        match statement {
            Statement::VariableDeclaration { variable } => {
                if self.scope().has_variable(&variable.identifier) {
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
                scope.push_variable(bound_var);
            }
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                if self.scope().has_variable(&variable.identifier) {
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
                self.emitter.emit_expression(&expression).expect("asd");
                self.emitter
                    .emit_instruction(Instruction::STO {
                        level: 0,
                        offset: 1000,
                    })
                    .expect("asd");
                let bound_var = BoundVariable {
                    position: variable.position,
                    identifier: variable.identifier.clone(),
                    data_type: variable.data_type.clone(),
                    value: Some(expression),
                    initialized: true,
                };
                self.scope_mut().push_variable(bound_var);
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

    fn begin_global_scope(&mut self, translation_unit: &TranslationUnit<'a>) {
        self.begin_scope();
        let functions = &translation_unit.functions;
        let statements = &translation_unit.global_statements;

        for statement in statements {
            if let Some(variable) = self.statement_to_variable(statement) {
                let identifier = variable.identifier;
                if self.global_scope().has_variable(&identifier) {
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
                let scope = self.global_scope_mut();
                scope.push_variable(bound_var);
            }
        }

        for function in functions {
            if self.global_scope().has_function(&function.identifier) {
                self.error_diag.borrow_mut().function_already_exists(
                    function.position.0,
                    function.position.1,
                    function.identifier,
                );
            }

            let scope = self.global_scope_mut();
            let bound_func = BoundFunction {
                identifier: function.identifier,
                return_type: function.return_type.clone(),
            };
            dbg!(&bound_func);
            scope.push_function(bound_func);
        }
    }

    fn end_global_scope(&mut self) {
        self.end_scope();
    }
    fn begin_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    fn end_scope(&mut self) {
        self.scopes.pop().expect("A scope to pop");
    }

    fn begin_function(&mut self, function: &Function<'a>) {
        let mut params = Vec::new();
        for parameter in &function.parameters {
            params.push(BoundParameter {
                identifier: parameter.identifier.clone(),
                data_type: parameter.data_type.clone(),
            });
        }

        self.scope_mut().push_function(BoundFunction {
            identifier: function.identifier.clone(),
            return_type: function.return_type.clone(),
        });
        self.begin_scope();
    }

    fn end_function(&mut self) {
        self.end_scope();
    }

    fn scope_mut(&mut self) -> &mut Scope<'a> {
        self.scopes.last_mut().expect("A scope")
    }

    fn scope(&self) -> &Scope<'a> {
        self.scopes.last().expect("A scope")
    }

    fn global_scope_mut(&mut self) -> &mut Scope<'a> {
        self.scopes.first_mut().expect("Global scope")
    }

    fn global_scope(&self) -> &Scope<'a> {
        self.scopes.first().expect("Global scope")
    }

    fn statement_to_variable(&self, statement: &Statement<'a>) -> Option<&BoundVariable<'a>> {
        return match statement {
            Statement::VariableDeclaration { variable } => {
                self.scope().get_variable(variable.identifier)
            }
            Statement::VariableDeclarationAndAssignment { variable, .. } => {
                self.scope().get_variable(variable.identifier)
            }
            _ => {
                panic!("Invalid statement type")
            }
        };
    }
}
