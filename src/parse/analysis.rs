use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::marker::PhantomData;
use std::mem::size_of;
use std::rc::Rc;

use crate::emit::emitter::{Emitter, Instruction};
use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::evaluate::Evaluator;
use crate::parse::parser::{
    DataType, Expression, Function, Statement, TranslationUnit, UnaryOperator,
};

#[derive(Default)]
struct FunctionScope<'a> {
    variables: HashMap<&'a str, BoundVariable<'a>>,
}

impl<'a> FunctionScope<'a> {
    fn push_variable(&mut self, variable: BoundVariable<'a>) {
        self.variables.insert(variable.identifier, variable);
    }

    fn get_variable(&self, identifier: &str) -> Option<&BoundVariable<'a>> {
        self.variables.get(identifier)
    }

    fn has_variable(&self, identifier: &str) -> bool {
        self.variables.contains_key(identifier)
    }
}

#[derive(Default)]
struct GlobalScope<'a> {
    variables: HashMap<&'a str, BoundVariable<'a>>,
    functions: HashMap<&'a str, BoundFunction<'a>>,
}

impl<'a> GlobalScope<'a> {
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
    global_scope: GlobalScope<'a>,
    /// Current stack of function scopes. The initial scope is the global scope that should be
    /// popped
    /// at the end of the analysis.
    function_scopes: Vec<FunctionScope<'a>>,
    error_diag: Rc<RefCell<ErrorDiagnosis<'a, 'b>>>,
    evaluator: Evaluator<'a>,
    emitter: Emitter<T>,
}

#[derive(Clone, Debug)]
pub struct BoundFunction<'a> {
    pub identifier: &'a str,
    pub return_type: DataType<'a>,
    pub block: BoundBlock<'a>,
    pub parameters: Vec<BoundParameter<'a>>,
}

#[derive(Clone, Debug)]
pub struct BoundBlock<'a> {
    pub statements: Vec<Statement<'a>>,
}

#[derive(Clone, Debug)]
pub struct BoundVariable<'a> {
    position: (u32, u32),
    identifier: &'a str,
    data_type: DataType<'a>,
    value: Option<Expression<'a>>,
    initialized: bool,
}

impl<'a> BoundVariable<'a> {
    pub fn size(&self) -> usize {
        match self.data_type {
            DataType::Xxlpp => size_of::<i64>(),
            DataType::Pp => size_of::<i32>(),
            DataType::Spp => size_of::<i16>(),
            DataType::Xspp => size_of::<i8>(),
            DataType::P => size_of::<char>(),
            _ => panic!(""),
        }
    }
}

#[derive(Clone, Debug)]
pub struct BoundParameter<'a> {
    pub identifier: &'a str,
    pub data_type: DataType<'a>,
}

impl<'a, 'b, T: Write> SemanticAnalyzer<'a, 'b, T> {
    pub fn new(error_diag: Rc<RefCell<ErrorDiagnosis<'a, 'b>>>, emitter: Emitter<T>) -> Self {
        Self {
            function_scopes: Vec::default(),
            global_scope: GlobalScope::default(),
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
            .emit_instruction(Instruction::JMP { address: 0 });
        self.emitter.emit_all().expect("OOF");
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
        match &statement {
            Statement::VariableDeclaration { variable } => {
                if self.function_scope().has_variable(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }

                let scope = self.function_scope_mut();
                let bound_var = BoundVariable {
                    position: variable.position,
                    identifier: variable.identifier,
                    value: None,
                    initialized: false,
                    data_type: variable.data_type.clone(),
                };
                dbg!(&bound_var);
                scope.push_variable(bound_var);
            }
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                if self.function_scope().has_variable(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                    return;
                }

                if self.eval(&expression) != variable.data_type {
                    self.error_diag.borrow_mut().invalid_type(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }
                dbg!(&expression);
                let bound_var = BoundVariable {
                    position: variable.position,
                    identifier: variable.identifier.clone(),
                    data_type: variable.data_type.clone(),
                    value: Some(expression.clone()),
                    initialized: true,
                };
                self.function_scope_mut().push_variable(bound_var);
            }
            _ => {}
        }
        self.emitter.emit_statement(&statement);
    }

    pub fn eval(&self, expr: &Expression<'a>) -> DataType<'a> {
        return match expr {
            Expression::PpExpression { .. } => DataType::Pp,
            Expression::PExpression { .. } => DataType::P,
            Expression::BoobaExpression { .. } => DataType::Booba,
            Expression::YarnExpression { .. } => DataType::Yarn,
            Expression::UnaryExpression { operand, op, .. } => {
                let data_type = self.eval(operand);
                return match op {
                    UnaryOperator::Not => match data_type {
                        DataType::Booba => data_type,
                        _ => panic!("Invalid type for unary operator"),
                    },
                    UnaryOperator::Negate => match data_type {
                        DataType::Xxlpp | DataType::Pp | DataType::Spp | DataType::Xspp => {
                            data_type
                        }
                        _ => panic!("Invalid type for unary operator"),
                    },
                };
            }
            Expression::BinaryExpression { lhs, rhs, op, .. } => {
                let lhs_data_type = self.eval(lhs);
                let rhs_data_type = self.eval(rhs);
                assert_eq!(lhs_data_type, rhs_data_type, "Data types do not match");
                // TODO: Check whether the binary operator is available for the given data type.
                lhs_data_type
            }
            Expression::IdentifierExpression { identifier, .. } => self
                .function_scope()
                .get_variable(identifier)
                .unwrap()
                .data_type
                .clone(),
            _ => DataType::Nopp,
        };
    }

    fn begin_global_scope(&mut self, translation_unit: &TranslationUnit<'a>) {
        self.begin_function_scope();
        let functions = &translation_unit.functions;
        let statements = &translation_unit.global_statements;

        for statement in statements {
            if let Some(variable) = match statement {
                Statement::VariableDeclaration { variable } => {
                    self.global_scope().get_variable(variable.identifier)
                }
                Statement::VariableDeclarationAndAssignment { variable, .. } => {
                    self.global_scope().get_variable(variable.identifier)
                }
                _ => {
                    panic!("Invalid statement type")
                }
            } {
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
                self.global_scope_mut().push_variable(bound_var);
            }
            self.emitter.begin_scope();
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
            let block = BoundBlock {
                statements: function.block.statements.clone(),
            };
            let bound_func = BoundFunction {
                identifier: function.identifier,
                return_type: function.return_type.clone(),
                block,
                parameters: function
                    .parameters
                    .iter()
                    .map(|param| BoundParameter {
                        identifier: param.identifier,
                        data_type: param.data_type.clone(),
                    })
                    .collect::<Vec<BoundParameter<'a>>>()
                    .clone(),
            };
            dbg!(&bound_func);
            scope.push_function(bound_func);
        }
    }

    fn end_global_scope(&mut self) {
        self.emitter.end_scope();
    }
    fn begin_function_scope(&mut self) {
        self.function_scopes.push(FunctionScope::default());
    }

    fn end_function_scope(&mut self) {
        self.function_scopes.pop().expect("A scope to pop");
    }

    fn begin_function(&mut self, function: &Function<'a>) {
        let mut params = Vec::new();
        for parameter in &function.parameters {
            params.push(BoundParameter {
                identifier: parameter.identifier.clone(),
                data_type: parameter.data_type.clone(),
            });
        }

        self.global_scope_mut().push_function(BoundFunction {
            identifier: function.identifier.clone(),
            return_type: function.return_type.clone(),
            block: BoundBlock {
                statements: function.block.statements.clone(),
            },
            parameters: function
                .parameters
                .iter()
                .map(|param| BoundParameter {
                    identifier: param.identifier,
                    data_type: param.data_type.clone(),
                })
                .collect::<Vec<BoundParameter<'a>>>()
                .clone(),
        });
        self.begin_function_scope();
    }

    fn end_function(&mut self) {
        self.end_function_scope();
    }

    fn function_scope_mut(&mut self) -> &mut FunctionScope<'a> {
        self.function_scopes.last_mut().expect("A scope")
    }

    fn function_scope(&self) -> &FunctionScope<'a> {
        self.function_scopes.last().expect("A scope")
    }

    fn global_scope_mut(&mut self) -> &mut GlobalScope<'a> {
        &mut self.global_scope
    }

    fn global_scope(&self) -> &GlobalScope<'a> {
        &self.global_scope
    }
}
