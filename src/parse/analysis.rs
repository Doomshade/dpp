use std::collections::HashMap;
use std::io::Write;

use crate::emit::emitter::{Address, DebugKeyword, Emitter, Instruction};
use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::parser::{
    DataType, Expression, Function, Statement, TranslationUnit, UnaryOperator, Variable,
};

#[derive(Clone, Debug, Default)]
pub struct FunctionScope<'a> {
    scope: Scope<'a>,
}

#[derive(Clone, Debug, Default)]
pub struct Scope<'a> {
    /// The current position in the stack frame. This is used to calculate the absolute position
    /// of the variable in the stack frame.
    current_position: u32,
    /// This is basically the symbol table.
    variables: HashMap<&'a str, std::rc::Rc<BoundVariable<'a>>>,
}

impl<'a> Scope<'a> {
    fn push_variable(&mut self, mut variable: BoundVariable<'a>) {
        variable.position_in_scope = self.current_position;
        self.current_position += ((variable.size() as u32 - 1) / 4) + 1;
        self.variables
            .insert(variable.identifier, std::rc::Rc::new(variable));
    }

    pub fn get_variable(&self, identifier: &str) -> Option<&std::rc::Rc<BoundVariable<'a>>> {
        self.variables.get(identifier)
    }

    pub fn has_variable(&self, identifier: &str) -> bool {
        self.variables.contains_key(identifier)
    }
}

#[derive(Clone, Debug, Default)]
pub struct GlobalScope<'a> {
    scope: Scope<'a>,
    functions: HashMap<&'a str, BoundFunction<'a>>,
}

impl<'a> GlobalScope<'a> {
    fn push_function(&mut self, function: BoundFunction<'a>) {
        self.functions.insert(function.identifier, function);
    }

    fn push_variable(&mut self, variable: BoundVariable<'a>) {
        self.scope.push_variable(variable);
    }

    pub fn scope(&self) -> &Scope<'a> {
        &self.scope
    }

    pub fn get_function(&self, identifier: &str) -> Option<&BoundFunction<'a>> {
        self.functions.get(identifier)
    }

    fn has_function(&self, identifier: &str) -> bool {
        self.functions.contains_key(identifier)
    }
}

pub struct SemanticAnalyzer<'a, 'b, T>
where
    T: Write,
{
    global_scope: std::rc::Rc<std::cell::RefCell<GlobalScope<'a>>>,
    /// Current stack of function scopes. The initial scope is the global scope that should be
    /// popped
    /// at the end of the analysis.
    function_scopes: std::rc::Rc<std::cell::RefCell<Vec<FunctionScope<'a>>>>,
    error_diag: std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
    emitter: Emitter<'a, T>,
}

#[derive(Clone, Debug)]
pub struct BoundFunction<'a> {
    identifier: &'a str,
    return_type: DataType<'a>,
    block: BoundBlock<'a>,
    parameters: Vec<BoundParameter<'a>>,
}

impl<'a> BoundFunction<'a> {
    pub fn identifier(&self) -> &'a str {
        self.identifier
    }
    pub fn return_type(&self) -> &DataType<'a> {
        &self.return_type
    }
    pub fn block(&self) -> &BoundBlock<'a> {
        &self.block
    }
    pub fn parameters(&self) -> &Vec<BoundParameter<'a>> {
        &self.parameters
    }
}

#[derive(Clone, Debug)]
pub struct BoundBlock<'a> {
    pub statements: Vec<Statement<'a>>,
}

#[derive(Clone, Debug)]
pub struct BoundVariable<'a> {
    /// Returns the absolute position of the variable in the scope. The absolute position
    /// is the position relative to the base pointer. The first variable has the position 0, the
    /// second has a position of `((first_variable_size - 1) / 4) + 1` - in essence if the size of
    /// the first variable is 1...4 bytes, then the position is 1, if the size is 5...8 bytes, then
    /// the position is 2, and so on. This is because the PL/0 machine has a word size of 4 bytes
    /// and if we want to store something larger than that we have to store multiple words.
    position_in_scope: u32,
    identifier: &'a str,
    data_type: DataType<'a>,
    size: usize,
    value: Option<Expression<'a>>,
}

impl<'a> BoundVariable<'a> {
    fn new(variable: &Variable<'a>, expression: Option<&Expression<'a>>) -> Self {
        let identifier = variable.identifier.clone();
        let size = variable.data_type.size();
        let data_type = variable.data_type.clone();
        return if let Some(expression) = expression {
            BoundVariable {
                position_in_scope: 0,
                identifier,
                size,
                data_type,
                value: Some(expression.clone()),
            }
        } else {
            BoundVariable {
                position_in_scope: 0,
                identifier,
                size,
                data_type,
                value: None,
            }
        };
    }

    pub fn initialized(&self) -> bool {
        self.value.is_some()
    }

    pub fn size(&self) -> usize {
        self.data_type.size()
    }

    pub fn position_in_scope(&self) -> u32 {
        self.position_in_scope
    }
    pub fn identifier(&self) -> &'a str {
        self.identifier
    }
    pub fn data_type(&self) -> &DataType<'a> {
        &self.data_type
    }
    pub fn value(&self) -> &Option<Expression<'a>> {
        &self.value
    }
}

#[derive(Clone, Debug)]
pub struct BoundParameter<'a> {
    pub identifier: &'a str,
    pub data_type: DataType<'a>,
}

impl<'a, 'b, T: Write> SemanticAnalyzer<'a, 'b, T> {
    pub fn new(
        error_diag: std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
        function_scopes: std::rc::Rc<std::cell::RefCell<Vec<FunctionScope<'a>>>>,
        global_scope: std::rc::Rc<std::cell::RefCell<GlobalScope<'a>>>,
        emitter: Emitter<'a, T>,
    ) -> Self {
        Self {
            function_scopes,
            global_scope,
            error_diag,
            emitter,
        }
    }

    fn is_in_function_scope(&self) -> bool {
        self.function_scopes.borrow().last().is_some()
    }

    pub fn analyze(&mut self, translation_unit: TranslationUnit<'a>) {
        {
            // Analyze global statements and functions.
            for statement in translation_unit.global_statements {
                self.analyze_global_statement(statement);
            }
            // The last instruction will be the JMP to 0 - indicating exit.
            self.emitter.emit_debug_info(DebugKeyword::REGS);
            self.emitter.emit_instruction(Instruction::JMP {
                address: Address::Label(String::from("main")),
            });

            for function in translation_unit.functions {
                self.analyze_function(function);
            }
        }
        // The last instruction will be the JMP to 0 - indicating exit.
        self.emitter.emit_instruction(Instruction::JMP {
            address: Address::Absolute(0),
        });
        self.emitter.emit_all().expect("OOF");
    }

    fn analyze_function(&mut self, function: Function<'a>) {
        self.begin_function(&function);
        {
            if function.return_type != DataType::Nopp {
                // If it's anything other than Nopp, then we require the function to have
                // a return statement at the very end.
                let last_statement = function.block.statements.last();
                if let Some(last_statement) = last_statement {
                    if let Statement::ByeStatement { .. } = last_statement {
                        // Do nothing
                    } else {
                        self.error_diag.borrow_mut().missing_return_statement(
                            function.block.position.0,
                            function.block.position.1,
                        );
                    }
                } else {
                    self.error_diag.borrow_mut().missing_return_statement(
                        function.block.position.0,
                        function.block.position.1,
                    );
                }
            }
            for statement in function.block.statements {
                self.analyze_statement(statement);
            }
        }
        self.end_function();
    }

    fn analyze_global_statement(&mut self, statement: Statement<'a>) {
        match &statement {
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                if self.has_variable_in_scope(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                    return;
                }

                let data_type = self.eval(&expression);
                let mut matching_data_type = false;
                if let DataType::Number(..) = data_type {
                    if let DataType::Number(..) = variable.data_type {
                        matching_data_type = true;
                    }
                }
                if !matching_data_type {
                    matching_data_type = data_type == variable.data_type;
                }
                assert!(matching_data_type, "Data types do not match");

                if self.eval(&expression) != variable.data_type {
                    self.error_diag.borrow_mut().invalid_type(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }
                dbg!(&expression);
                let bound_var = BoundVariable::new(variable, Some(expression));
                self.global_scope.borrow_mut().push_variable(bound_var);
            }
            _ => {}
        }
        self.emitter.emit_statement(&statement);
    }

    fn has_variable_in_scope(&self, identifier: &str) -> bool {
        return if let Some(scope) = self.function_scopes.borrow().last() {
            scope.scope.has_variable(identifier)
        } else {
            false
        };
    }

    fn analyze_statement(&mut self, statement: Statement<'a>) {
        match &statement {
            Statement::VariableDeclaration { variable } => {
                if self.has_variable_in_scope(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }

                let mut ref_mut = self.function_scopes.borrow_mut();
                let function_scope = ref_mut.last_mut().unwrap();
                let bound_var = BoundVariable::new(variable, None);
                dbg!(&bound_var);
                function_scope.scope.push_variable(bound_var);
            }
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                if self.has_variable_in_scope(&variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                    return;
                }

                let data_type = self.eval(&expression);
                let mut matching_data_type = false;
                if let DataType::Number(..) = data_type {
                    if let DataType::Number(..) = variable.data_type {
                        matching_data_type = true;
                    }
                }
                if !matching_data_type {
                    matching_data_type = data_type == variable.data_type;
                }
                assert!(matching_data_type, "Data types do not match");

                if self.eval(&expression) != variable.data_type {
                    self.error_diag.borrow_mut().invalid_type(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }
                dbg!(&expression);
                let bound_var = BoundVariable::new(variable, Some(expression));
                self.function_scopes
                    .borrow_mut()
                    .last_mut()
                    .unwrap()
                    .scope
                    .push_variable(bound_var);
            }
            _ => {}
        }
        self.emitter.emit_statement(&statement);
    }

    pub fn eval(&self, expr: &Expression<'a>) -> DataType<'a> {
        return match expr {
            Expression::NumberExpression { number_type, .. } => {
                DataType::Number(number_type.clone())
            }
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
                        DataType::Number(..) => data_type,
                        _ => panic!("Invalid type for unary operator"),
                    },
                };
            }
            Expression::BinaryExpression { lhs, rhs, .. } => {
                let lhs_data_type = self.eval(lhs);
                let rhs_data_type = self.eval(rhs);
                assert_eq!(lhs_data_type, rhs_data_type, "Data types do not match");
                // TODO: Check whether the binary operator is available for the given data type.
                lhs_data_type
            }
            Expression::IdentifierExpression { identifier, .. } => {
                let function_scopes = self.function_scopes.borrow_mut();
                if let Some(current_function_scope) = function_scopes.last() {
                    if let Some(variable) = current_function_scope.scope.get_variable(identifier) {
                        return variable.data_type.clone();
                    }
                }
                if let Some(global_variable) =
                    self.global_scope.borrow().scope.get_variable(identifier)
                {
                    return global_variable.data_type.clone();
                } else {
                    panic!("Variable not found");
                }
            }
            Expression::FunctionCall { identifier, .. } => {
                if let Some(global_function) = self.global_scope.borrow().get_function(identifier) {
                    return global_function.return_type.clone();
                } else {
                    panic!("Function not found");
                }
            }
            _ => DataType::Nopp,
        };
    }

    fn begin_function_scope(&mut self) {
        self.function_scopes
            .borrow_mut()
            .push(FunctionScope::default());
    }

    fn end_function_scope(&mut self) {
        self.function_scopes
            .borrow_mut()
            .pop()
            .expect("A scope to pop");
    }

    fn begin_function(&mut self, function: &Function<'a>) {
        let mut params = Vec::new();
        for parameter in &function.parameters {
            params.push(BoundParameter {
                identifier: parameter.identifier.clone(),
                data_type: parameter.data_type.clone(),
            });
        }

        self.global_scope.borrow_mut().push_function(BoundFunction {
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
        self.emitter.emit_label(function.identifier);
    }

    fn end_function(&mut self) {
        self.end_function_scope();
    }
}
