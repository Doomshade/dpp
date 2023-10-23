use crate::parse::{Expression, Function, SemanticAnalyzer, Statement, UnaryOperator};
use crate::parse::analysis::SymbolTable;
use crate::parse::parser::{DataType, TranslationUnit};

impl<'a, 'b> SemanticAnalyzer<'a, 'b> {
    pub fn analyze(&mut self, translation_unit: &TranslationUnit<'a>) {
        // Analyze global statements.
        translation_unit.global_statements().iter().for_each(|statement| self.analyze_global_statement(statement));

        // Analyze the parsed functions.
        translation_unit.functions().iter().for_each(|function| self.analyze_function(function));

        if !self.symbol_table().find_function("main").is_some() {
            self.error_diag.borrow_mut().no_main_method_found_error();
        }
    }

    pub fn into_symbol_table(self) -> SymbolTable<'a> {
        self.symbol_table
    }

    fn analyze_function(&mut self, function: &Function<'a>) {
        self.begin_function(&function);
        for statement in function.block().statements() {
            self.analyze_statement(statement);
        }
        if function.return_type() != &DataType::Nopp {
            // If it's anything other than Nopp, then we require the function to have
            // a return statement at the very end.
            let last_statement = function.block().statements().last();
            if let Some(Statement::Bye { .. }) = last_statement {
                // Do nothing.
            } else {
                self.error_diag.borrow_mut().missing_return_statement(
                    function.block().position().0,
                    function.block().position().1,
                );
            }
        }
        self.end_function();
    }

    fn analyze_global_statement(&mut self, statement: &Statement<'a>) {
        match &statement {
            Statement::VariableDeclaration { variable } => {
                if self.symbol_table().find_local_variable(variable.identifier(), self.current_function).is_some() {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position().0,
                        variable.position().1,
                        variable.identifier(),
                    );
                    return;
                }

                if let Some(expression) = variable.value() {
                    let data_type = self.eval(expression);
                    let mut matching_data_type = false;
                    if let DataType::Number(..) = data_type {
                        if let DataType::Number(..) = variable.data_type() {
                            matching_data_type = true;
                        }
                    }
                    if !matching_data_type {
                        matching_data_type = &data_type == variable.data_type();
                    }
                    assert!(matching_data_type, "Data types do not match");
                }
                self.symbol_table_mut().push_global_variable(variable.clone());
            }
            _ => {}
        }
    }

    fn analyze_statement(&mut self, statement: &Statement<'a>) {
        match &statement {
            Statement::VariableDeclaration { variable } => {
                if self.symbol_table().find_local_variable(variable.identifier(), self.current_function).is_some
                () {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position().0,
                        variable.position().1,
                        variable.identifier(),
                    );
                }

                if let Some(expression) = variable.value() {
                    let data_type = self.eval(expression);
                    assert_eq!(&data_type, variable.data_type(), "Data types do not match");

                    if &self.eval(expression) != variable.data_type() {
                        self.error_diag.borrow_mut().invalid_type(
                            variable.position().0,
                            variable.position().1,
                            variable.identifier(),
                        );
                    }
                }
                self.symbol_table_mut().push_local_variable(variable.clone());
                // dbg!(&expression);
            }
            Statement::Expression { expression, .. } => {
                // Must check whether the function call expression has valid amount of arguments.
                if let Expression::FunctionCall {
                    identifier,
                    arguments,
                    position,
                } = expression
                {
                    if let Some(function) = self.symbol_table().find_function(identifier) {
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
            Statement::While {
                expression,
                statement,
                position,
            } => {
                let data_type = self.eval(expression);
                if !matches!(data_type, DataType::Booba) {
                    self.error_diag.borrow_mut().invalid_data_type(
                        position.0,
                        position.1,
                        DataType::Booba,
                        &data_type,
                    );
                }
                self.analyze_statement(statement);
            }
            Statement::Block { block, .. } => {
                block
                    .statements()
                    .iter()
                    .for_each(|statement| self.analyze_statement(statement));
            }
            Statement::Bye { .. } => {}
            Statement::If {
                expression,
                statement,
                position,
            } => {
                let data_type = self.eval(expression);

                if !matches!(data_type, DataType::Booba) {
                    self.error_diag.borrow_mut().invalid_data_type(
                        position.0,
                        position.1,
                        DataType::Booba,
                        &data_type,
                    )
                }
                self.analyze_statement(statement);
            }
            Statement::IfElse {expression, statement, position, else_statement} => {
                let data_type = self.eval(expression);

                if !matches!(data_type, DataType::Booba) {
                    self.error_diag.borrow_mut().invalid_data_type(
                        position.0,
                        position.1,
                        DataType::Booba,
                        &data_type,
                    )
                }
                self.analyze_statement(statement);
                self.analyze_statement(else_statement);
            }
            _ => {
                todo!("Analyzing {:?}", statement)
            }
        };
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
            Expression::Binary { lhs, rhs, op, .. } => {
                let lhs_data_type = self.eval(lhs);
                let rhs_data_type = self.eval(rhs);
                assert_eq!(lhs_data_type, rhs_data_type, "Data types do not match");
                // TODO: Check whether the binary operator is available for the given data type.
                use crate::parse::BinaryOperator::*;
                match op {
                    Add | Subtract | Multiply | Divide => lhs_data_type,
                    NotEqual | Equal | GreaterThan | GreaterThanOrEqual | LessThan
                    | LessThanOrEqual => DataType::Booba,
                }
            }
            Expression::Identifier { identifier, .. } => {
                if let Some(variable) = self.symbol_table().find_variable(identifier, self.current_function) {
                    return variable.data_type().clone();
                }
                panic!("{}", format!("Variable {identifier} not found"));
            }
            Expression::FunctionCall { identifier, .. } => {
                if let Some(global_function) = self.symbol_table().find_function(identifier) {
                    return global_function.return_type().clone();
                }
                panic!("{}", format!("Function {identifier} not found"));
            }
            _ => DataType::Nopp,
        };
    }

    fn begin_function(&mut self, function: &Function<'a>) {
        self.current_function = Some(function.identifier());
        let mut ref_mut = self.symbol_table_mut();
        ref_mut.push_function(function.clone());
        function.parameters().iter().for_each(|parameter| ref_mut.push_local_variable(parameter.clone()));
    }

    fn end_function(&mut self) {
        self.current_function = None;
    }
}
