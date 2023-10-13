use std::collections::HashMap;
use std::io::Write;

use crate::emit::emitter::{Address, Emitter};
use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::parser::{
    DataType, Expression, Function, Statement, TranslationUnit, UnaryOperator, Variable,
};

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
        self.current_position += variable.size_in_instructions() as u32;
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

#[derive(Clone, Debug)]
pub struct FunctionScope<'a> {
    // TODO: Use Vec<Scope<'a>> because we allow nested scopes in functions.
    scope: Scope<'a>,
    function_identifier: &'a str,
}

impl<'a> FunctionScope<'a> {
    pub fn new(function_identifier: &'a str) -> Self {
        let mut scope = Scope::default();
        scope.current_position += 3;
        FunctionScope { scope, function_identifier }
    }

    pub fn has_variable(&self, identifier: &str) -> bool {
        self.scope.has_variable(identifier)
    }

    pub fn get_variable(&self, identifier: &str) -> Option<&std::rc::Rc<BoundVariable<'a>>> {
        self.scope.get_variable(identifier)
    }

    pub fn function_identifier(&self) -> &'a str {
        self.function_identifier
    }

    pub fn push_argument(&mut self, variable: BoundVariable<'a>) {}

    pub fn push_variable(&mut self, variable: BoundVariable<'a>) {
        self.scope.push_variable(variable);
    }

    pub fn push_scope(&mut self) {
        todo!("Not yet implemented.");
    }

    pub fn pop_scope(&mut self) {
        todo!("Not yet implemented.");
    }
}

#[derive(Clone, Debug)]
pub struct GlobalScope<'a> {
    scope: Scope<'a>,
    functions: HashMap<&'a str, BoundFunction<'a>>,
}

impl<'a> GlobalScope<'a> {
    pub fn new() -> Self {
        let mut scope = Scope::default();
        scope.current_position = 1000;
        GlobalScope {
            scope,
            functions: HashMap::new(),
        }
    }
    fn push_function(&mut self, function: BoundFunction<'a>) {
        self.functions.insert(function.identifier, function);
    }

    fn push_variable(&mut self, variable: BoundVariable<'a>) {
        self.scope.push_variable(variable);
    }

    pub fn has_variable(&self, identifier: &str) -> bool {
        self.scope.has_variable(identifier)
    }

    pub fn get_variable(&self, identifier: &str) -> Option<&std::rc::Rc<BoundVariable<'a>>> {
        self.scope.get_variable(identifier)
    }

    pub fn scope(&self) -> &Scope<'a> {
        &self.scope
    }

    pub fn get_function(&self, identifier: &str) -> Option<&BoundFunction<'a>> {
        self.functions.get(identifier)
    }

    pub fn has_function(&self, identifier: &str) -> bool {
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
    current_level: std::rc::Rc<std::cell::RefCell<u32>>,
    emitter: Emitter<'a, T>,
}

#[derive(Clone, Debug)]
pub struct BoundFunction<'a> {
    identifier: &'a str,
    return_type: DataType<'a>,
    block: BoundBlock<'a>,
    parameters: Vec<Variable<'a>>,
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
    pub fn parameters(&self) -> &Vec<Variable<'a>> {
        &self.parameters
    }

    pub fn parameters_size(&self) -> usize {
        self.parameters().iter().fold(0, |acc, parameter| acc +
            parameter.data_type.size_in_instructions())
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
        if let Some(expression) = expression {
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
        }
    }

    pub fn initialized(&self) -> bool {
        self.value.is_some()
    }

    pub fn size(&self) -> usize {
        self.data_type.size()
    }

    pub fn size_in_instructions(&self) -> usize {
        self.data_type.size_in_instructions()
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

impl<'a, 'b, T: Write> SemanticAnalyzer<'a, 'b, T> {
    pub fn new(
        error_diag: std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, 'b>>>,
        function_scopes: std::rc::Rc<std::cell::RefCell<Vec<FunctionScope<'a>>>>,
        global_scope: std::rc::Rc<std::cell::RefCell<GlobalScope<'a>>>,
        current_level: std::rc::Rc<std::cell::RefCell<u32>>,
        emitter: Emitter<'a, T>,
    ) -> Self {
        Self {
            function_scopes,
            global_scope,
            error_diag,
            current_level,
            emitter,
        }
    }

    fn is_in_function_scope(&self) -> bool {
        self.function_scopes.borrow().last().is_some()
    }

    pub fn analyze(&mut self, translation_unit: &TranslationUnit<'a>) {
        {
            // Analyze global statements and functions.
            for statement in &translation_unit.global_statements {
                self.analyze_global_statement(statement);
            }

            self.emitter.emit_main_call();

            // The last instruction will be the JMP to 0 - indicating exit.
            self.emitter.emit_jump(Address::Absolute(0));
            for function in &translation_unit.functions {
                self.analyze_function(function);
            }
        }

        self.emitter.emit_all().expect("OOF");
    }

    fn analyze_function(&mut self, function: &Function<'a>) {
        self.begin_function(&function);
        {
            for statement in &function.block.statements {
                self.analyze_statement(statement);
            }
            if function.return_type != DataType::Nopp {
                // If it's anything other than Nopp, then we require the function to have
                // a return statement at the very end.
                let last_statement = function.block.statements.last();
                if let Some(Statement::Bye { .. }) = last_statement {
                    // Do nothing.
                } else {
                    self.error_diag.borrow_mut().missing_return_statement(
                        function.block.position.0,
                        function.block.position.1,
                    );
                }
            }
        }
        self.end_function();
    }

    fn analyze_global_statement(&mut self, statement: &Statement<'a>) {
        match &statement {
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                if self.has_variable_in_local_function_scope(variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                    return;
                }

                let data_type = self.eval(expression);
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

                if self.eval(expression) != variable.data_type {
                    self.error_diag.borrow_mut().invalid_type(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }
                let bound_var = BoundVariable::new(variable, Some(expression));
                self.global_scope.borrow_mut().push_variable(bound_var);
                self.emitter.emit_statement(statement);
            }
            _ => {
                self.emitter.emit_statement(statement);
            }
        }
    }

    fn has_variable_in_local_function_scope(&self, identifier: &str) -> bool {
        self.function_scopes
            .borrow()
            .last()
            .is_some_and(|scope| scope.has_variable(identifier))
    }

    fn push_local_function_variable(&mut self, variable: BoundVariable<'a>) {
        if let Some(function_scope) = self.function_scopes.borrow_mut().last_mut() {
            function_scope.push_variable(variable);
        }
    }

    fn has_variable_in_global_scope(&self, identifier: &str) -> bool {
        self.global_scope.borrow().has_variable(identifier)
    }

    fn analyze_statement(&mut self, statement: &Statement<'a>) {
        match &statement {
            Statement::VariableDeclaration { variable } => {
                if self.has_variable_in_local_function_scope(variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }

                self.push_local_function_variable(BoundVariable::new(variable, None));
            }
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                if self.has_variable_in_local_function_scope(variable.identifier) {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                    return;
                }

                let data_type = self.eval(expression);
                assert_eq!(data_type, variable.data_type, "Data types do not match");

                if self.eval(expression) != variable.data_type {
                    self.error_diag.borrow_mut().invalid_type(
                        variable.position.0,
                        variable.position.1,
                        variable.identifier,
                    );
                }
                dbg!(&expression);
                self.push_local_function_variable(BoundVariable::new(variable, Some(expression)));
            }
            Statement::Expression { expression, .. } => {
                // Must check whether the function call expression has valid amount of arguments.
                if let Expression::FunctionCall {
                    identifier,
                    arguments,
                    position,
                } = expression
                {
                    if let Some(function) = self.global_scope.borrow().get_function(identifier) {
                        if function.parameters().len() != arguments.len() {
                            self.error_diag.borrow_mut().invalid_number_of_arguments(
                                position.0,
                                position.1,
                                identifier,
                                function.parameters().len(),
                                arguments.len(),
                            );
                        }
                    } else {
                        self.error_diag
                            .borrow_mut()
                            .function_does_not_exist(position.0, position.1);
                    }
                }
            }
            _ => {}
        }
        self.emitter.emit_statement(statement);
    }

    pub fn eval(&self, expr: &Expression<'a>) -> DataType<'a> {
        return match expr {
            Expression::Number { number_type, .. } => DataType::Number(number_type.clone()),
            Expression::P { .. } => DataType::P,
            Expression::Booba { .. } => DataType::Booba,
            Expression::Yarn { .. } => DataType::Yarn,
            Expression::Unary { operand, op, .. } => {
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
            Expression::Binary { lhs, rhs, .. } => {
                let lhs_data_type = self.eval(lhs);
                let rhs_data_type = self.eval(rhs);
                assert_eq!(lhs_data_type, rhs_data_type, "Data types do not match");
                // TODO: Check whether the binary operator is available for the given data type.
                lhs_data_type
            }
            Expression::Identifier { identifier, .. } => {
                let function_scopes = self.function_scopes.borrow_mut();
                if let Some(current_function_scope) = function_scopes.last() {
                    if let Some(variable) = current_function_scope.get_variable(identifier) {
                        return variable.data_type.clone();
                    }
                }
                if let Some(global_variable) = self.global_scope.borrow().get_variable(identifier) {
                    return global_variable.data_type.clone();
                }
                panic!("{}", format!("Variable {identifier} not found"));
            }
            Expression::FunctionCall { identifier, .. } => {
                if let Some(global_function) = self.global_scope.borrow().get_function(identifier) {
                    return global_function.return_type.clone();
                }
                panic!("{}", format!("Function {identifier} not found"));
            }
            _ => DataType::Nopp,
        };
    }

    fn begin_function_scope(&mut self, function_identifier: &'a str) {
        self.function_scopes.borrow_mut().push(FunctionScope::new(function_identifier));
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
            params.push(BoundVariable::new(parameter, None));
        }

        self.global_scope.borrow_mut().push_function(BoundFunction {
            identifier: function.identifier.clone(),
            return_type: function.return_type.clone(),
            block: BoundBlock {
                statements: function.block.statements.clone(),
            },
            parameters: function.parameters.clone(),
        });
        self.begin_function_scope(function.identifier);
        self.emitter.emit_function_label(function.identifier);
        self.emitter.emit_int(3);
        if !params.is_empty() {
            self.emitter.echo(format!("Loading {} arguments", params.len()).as_str());
            self.load_arguments(&params);
            self.emitter.echo(format!("{} arguments loaded", params.len()).as_str());
        }
    }

    fn load_arguments(&mut self, parameters: &Vec<BoundVariable<'a>>) {
        // Load the parameters into the stack from the callee function.
        // The parameters are on the stack in FIFO order like so: [n, n + 1, n + 2, ...].
        // To load them we have to get the total size of parameters and subtract it
        // each time we load a parameter.
        // for example:
        // ```FUNc foo(argc: pp, argv:xxlpp) {
        // ...
        // }
        // foo(1, 2);```
        // The parameters are loaded as follows:
        // The total size is 4 (pp) + 8 (xxlpp) = 12.
        // Load the variable at offset 12 (argc) and then subtract 4 from the offset.
        // Load the variable at offset 8 (argv) and then subtract 8 from the offset.
        // The LOD function only loads 32 bits, so for anything bigger
        // than that we need to LOD again.
        parameters
            .iter()
            .rev()
            .for_each(|parameter| self.push_local_function_variable(parameter.clone()));
        self.emitter.load_arguments(parameters);
    }

    fn end_function(&mut self) {
        self.end_function_scope();
    }
}
