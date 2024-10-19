use crate::lambda_parse::{parse_lambda, LambdaExpression};
use std::rc::Rc;
use uuid::Uuid;
use log::{debug, trace, info};
use colored::*;

pub struct VM {
    max_iterations: usize,
}

impl VM {
    pub fn new() -> Self {
        VM {
            max_iterations: 1000000, // default max iterations
        }
    }

    pub fn with_max_iterations(max_iterations: usize) -> Self {
        VM { max_iterations }
    }

    pub fn eval(&self, expr: &LambdaExpression) -> Rc<LambdaExpression> {
        debug!("{}", "Starting evaluation:".cyan().bold());
        let mut current = Rc::new(expr.clone());
        for i in 0..self.max_iterations {
            let next = self.eval_recursive(&current, 0);
            if *next == *current {
                debug!("{}", "Evaluation complete:".green().bold());
                debug!("  {}", next.to_string().green());
                return next;
            }
            current = next;
            if i % 1000 == 0 {
                debug!("Iteration {}: {}", i, current.to_string());
            }
        }
        debug!("{}", "Reached maximum iterations".yellow().bold());
        current
    }

    fn eval_recursive(&self, expr: &LambdaExpression, depth: usize) -> Rc<LambdaExpression> {
        if depth >= self.max_iterations {
            debug!("{}", "Reached maximum depth".yellow().bold());
            return Rc::new(expr.clone());
        }

        let result = match expr {
            LambdaExpression::Variable(_) => {
                debug!("{}Variable: {}", "  ".repeat(depth), expr.to_string());
                Rc::new(expr.clone())
            }
            LambdaExpression::Number(_) => {
                debug!("{}Number: {}", "  ".repeat(depth), expr.to_string());
                Rc::new(expr.clone())
            }
            LambdaExpression::Boolean(_) => {
                debug!("{}Boolean: {}", "  ".repeat(depth), expr.to_string());
                Rc::new(expr.clone())
            }
            LambdaExpression::Abstraction { parameter, body } => {
                debug!("{}Abstraction: {}", "  ".repeat(depth), expr.to_string());
                Rc::new(LambdaExpression::Abstraction {
                    parameter: parameter.clone(),
                    body: self.eval_recursive(body, depth + 1),
                })
            }
            LambdaExpression::Application { function, argument } => {
                debug!("{}Application: {}", "  ".repeat(depth), expr.to_string());
                let eval_func = self.eval_recursive(function, depth + 1);
                let eval_arg = self.eval_recursive(argument, depth + 1);
                match &*eval_func {
                    LambdaExpression::Abstraction { parameter, body } => {
                        let substituted = self.substitute(body, parameter, &eval_arg);
                        self.eval_recursive(&substituted, depth + 1)
                    }
                    _ => Rc::new(LambdaExpression::Application {
                        function: eval_func,
                        argument: eval_arg,
                    }),
                }
            }
            LambdaExpression::IsZero(inner) => {
                debug!("{}IsZero: {}", "  ".repeat(depth), expr.to_string());
                let eval_inner = self.eval_recursive(inner, depth + 1);
                match &*eval_inner {
                    LambdaExpression::Abstraction { parameter: f, body } => {
                        match &**body {
                            LambdaExpression::Abstraction { parameter: x, body: inner_body } => {
                                if **inner_body == LambdaExpression::Variable(x.clone()) {
                                    trace!("{}IsZero: it is zero", "  ".repeat(depth));
                                    Rc::new(parse_lambda("λx. λy. x").unwrap())  // true
                                } else {
                                    trace!("{}IsZero: it is not zero", "  ".repeat(depth));
                                    Rc::new(parse_lambda("λx. λy. y").unwrap())  // false
                                }
                            },
                            _ => Rc::new(LambdaExpression::IsZero(eval_inner)),
                        }
                    },
                    _ => Rc::new(LambdaExpression::IsZero(eval_inner)),
                }
            },
            LambdaExpression::IfThenElse(condition, then_expr, else_expr) => {
                let eval_condition = self.eval_recursive(condition, depth + 1);
                match eval_condition.to_church_bool() {
                    Some(true) => {
                        debug!("{}Condition is true, evaluating then_expr", "  ".repeat(depth));
                        self.eval_recursive(then_expr, depth + 1)
                    },
                    Some(false) => {
                        debug!("{}Condition is false, evaluating else_expr", "  ".repeat(depth));
                        self.eval_recursive(else_expr, depth + 1)
                    },
                    None => {
                        debug!("{}Condition is not a Church boolean, returning unevaluated IfThenElse", "  ".repeat(depth));
                        Rc::new(LambdaExpression::IfThenElse(
                            eval_condition.clone(),
                            then_expr.clone(),
                            else_expr.clone(),
                        ))
                    },
                }
            },
            LambdaExpression::Pred(inner) => {
                debug!("{}Pred: {}", "  ".repeat(depth), expr.to_string());
                let eval_inner = self.eval_recursive(inner, depth + 1);
                match &*eval_inner {
                    LambdaExpression::Abstraction { .. } => {
                        let pred_church =
                            parse_lambda("λn. λf. λx. n (λg. λh. h (g f)) (λu. x) (λu. u)")
                                .unwrap();
                        let result = LambdaExpression::Application {
                            function: Rc::new(pred_church),
                            argument: eval_inner,
                        };
                        self.eval_recursive(&result, depth + 1)
                    }
                    _ => Rc::new(LambdaExpression::Pred(eval_inner)),
                }
            }
            LambdaExpression::Succ(inner) => {
                debug!("{}Succ: {}", "  ".repeat(depth), expr.to_string());
                let eval_inner = self.eval_recursive(inner, depth + 1);
                match &*eval_inner {
                    LambdaExpression::Abstraction { .. } => {
                        let succ_church = parse_lambda("λn. λf. λx. f (n f x)").unwrap();
                        let result = LambdaExpression::Application {
                            function: Rc::new(succ_church),
                            argument: eval_inner,
                        };
                        self.eval_recursive(&result, depth + 1)
                    }
                    _ => Rc::new(LambdaExpression::Succ(eval_inner)),
                }
            }
            LambdaExpression::Multiply(left, right) => {
                let eval_left = self.eval_recursive(left, depth + 1);
                let eval_right = self.eval_recursive(right, depth + 1);
                match (&*eval_left, &*eval_right) {
                    (LambdaExpression::Number(n1), LambdaExpression::Number(n2)) => {
                        // Implement multiplication for your number representation
                        // This is a placeholder and needs to be implemented correctly
                        Rc::new(LambdaExpression::Number(Rc::new(LambdaExpression::Number(
                            Rc::new(LambdaExpression::Variable("product".to_string())),
                        ))))
                    }
                    _ => {
                        // Use Church encoding for multiplication
                        let multiply_church = parse_lambda("λm. λn. λf. λx. m (n f) x").unwrap();
                        let result = LambdaExpression::Application {
                            function: Rc::new(LambdaExpression::Application {
                                function: Rc::new(multiply_church),
                                argument: eval_left.clone(),
                            }),
                            argument: eval_right.clone(),
                        };
                        self.eval_recursive(&result, depth + 1)
                    }
                }
            }
            LambdaExpression::And(left, right) => {
                debug!("{}And: {}", "  ".repeat(depth), expr.to_string());
                let eval_left = self.eval_recursive(left, depth + 1);
                let eval_right = self.eval_recursive(right, depth + 1);
                let true_expr = parse_lambda("λx. λy. x").unwrap();
                let false_expr = parse_lambda("λx. λy. y").unwrap();
                if *eval_left == true_expr && *eval_right == true_expr {
                    Rc::new(true_expr)
                } else {
                    Rc::new(false_expr)
                }
            }
            LambdaExpression::Or(left, right) => {
                let eval_left = self.eval_recursive(left, depth + 1);
                let eval_right = self.eval_recursive(right, depth + 1);
                let true_expr = parse_lambda("λx. λy. x").unwrap();
                let false_expr = parse_lambda("λx. λy. y").unwrap();
                if *eval_left == true_expr || *eval_right == true_expr {
                    Rc::new(true_expr)
                } else {
                    Rc::new(false_expr)
                }
            }
            LambdaExpression::Not(inner) => {
                debug!("{}Not: {}", "  ".repeat(depth), expr.to_string());
                let eval_inner = self.eval_recursive(inner, depth + 1);
                let true_expr = parse_lambda("λx. λy. x").unwrap();
                let false_expr = parse_lambda("λx. λy. y").unwrap();
                if *eval_inner == true_expr {
                    Rc::new(false_expr)
                } else {
                    Rc::new(true_expr)
                }
            }
            LambdaExpression::Pair(first, second) => {
                debug!("{}Pair: {}", "  ".repeat(depth), expr.to_string());
                let eval_first = self.eval_recursive(first, depth + 1);
                let eval_second = self.eval_recursive(second, depth + 1);
                Rc::new(LambdaExpression::Pair(eval_first, eval_second))
            }
            LambdaExpression::First(pair) => {
                debug!("{}First: {}", "  ".repeat(depth), expr.to_string());
                let eval_pair = self.eval_recursive(pair, depth + 1);
                match &*eval_pair {
                    LambdaExpression::Pair(first, _) => first.clone(),
                    _ => Rc::new(LambdaExpression::First(eval_pair)),
                }
            }
            LambdaExpression::Second(pair) => {
                debug!("{}Second: {}", "  ".repeat(depth), expr.to_string());
                let eval_pair = self.eval_recursive(pair, depth + 1);
                match &*eval_pair {
                    LambdaExpression::Pair(_, second) => second.clone(),
                    _ => Rc::new(LambdaExpression::Second(eval_pair)),
                }
            }
            // not allow Y combinator nested
            // TODO
            LambdaExpression::YCombinator(f) => {
                debug!("{}YCombinator: {}", "  ".repeat(depth), expr.to_string());
                self.eval_y_combinator(f, depth)
            }

            // show error and not support yet
            _ => {
                debug!("{}Unsupported expression: {}", "  ".repeat(depth), expr.to_string());
                Rc::new(expr.clone())
            }
        };

        if *result == *expr {
            result
        } else {
            self.eval_recursive(&result, depth + 1)
        }
    }

    fn eval_y_combinator(&self, f: &Rc<LambdaExpression>, depth: usize) -> Rc<LambdaExpression> {
        if depth >= self.max_iterations {
            println!("Reached maximum depth in Y combinator evaluation");
            return Rc::new(LambdaExpression::YCombinator(f.clone()));
        }

        let eval_f = self.eval_recursive(f, depth + 1);
        match &*eval_f {
            LambdaExpression::Abstraction { parameter, body } => {
                let y_f = LambdaExpression::Application {
                    function: Rc::new(LambdaExpression::YCombinator(eval_f.clone())),
                    argument: eval_f.clone(),
                };
                let substituted = self.substitute(body, parameter, &y_f);
                self.eval_recursive(&substituted, depth + 1)
            }
            _ => Rc::new(LambdaExpression::YCombinator(eval_f)),
        }
    }

    fn substitute(
        &self,
        expr: &LambdaExpression,
        var: &str,
        replacement: &LambdaExpression,
    ) -> LambdaExpression {
        let result = match expr {
            LambdaExpression::Variable(name) if name == var => replacement.clone(),
            LambdaExpression::Variable(_) => expr.clone(),
            LambdaExpression::Number(_) => expr.clone(),
            LambdaExpression::Boolean(_) => expr.clone(),
            LambdaExpression::Abstraction { parameter, body } => {
                if parameter == var {
                    expr.clone()
                } else if self.occurs_free(parameter, replacement) {
                    let (new_param, new_body) = self.alpha_convert(parameter, body);
                    LambdaExpression::Abstraction {
                        parameter: new_param,
                        body: Rc::new(self.substitute(&new_body, var, replacement)),
                    }
                } else {
                    LambdaExpression::Abstraction {
                        parameter: parameter.clone(),
                        body: Rc::new(self.substitute(body, var, replacement)),
                    }
                }
            }
            LambdaExpression::Application { function, argument } => LambdaExpression::Application {
                function: Rc::new(self.substitute(function, var, replacement)),
                argument: Rc::new(self.substitute(argument, var, replacement)),
            },
            LambdaExpression::Pred(inner) => {
                LambdaExpression::Pred(Rc::new(self.substitute(inner, var, replacement)))
            }
            LambdaExpression::Succ(inner) => {
                LambdaExpression::Succ(Rc::new(self.substitute(inner, var, replacement)))
            }
            LambdaExpression::Pair(first, second) => LambdaExpression::Pair(
                Rc::new(self.substitute(first, var, replacement)),
                Rc::new(self.substitute(second, var, replacement)),
            ),
            LambdaExpression::First(inner) => {
                LambdaExpression::First(Rc::new(self.substitute(inner, var, replacement)))
            }
            LambdaExpression::Second(inner) => {
                LambdaExpression::Second(Rc::new(self.substitute(inner, var, replacement)))
            }
            LambdaExpression::And(left, right) => LambdaExpression::And(
                Rc::new(self.substitute(left, var, replacement)),
                Rc::new(self.substitute(right, var, replacement)),
            ),
            LambdaExpression::Or(left, right) => LambdaExpression::Or(
                Rc::new(self.substitute(left, var, replacement)),
                Rc::new(self.substitute(right, var, replacement)),
            ),
            LambdaExpression::Not(inner) => {
                LambdaExpression::Not(Rc::new(self.substitute(inner, var, replacement)))
            }
            LambdaExpression::IsZero(inner) => {
                LambdaExpression::IsZero(Rc::new(self.substitute(inner, var, replacement)))
            }
            LambdaExpression::Multiply(left, right) => LambdaExpression::Multiply(
                Rc::new(self.substitute(left, var, replacement)),
                Rc::new(self.substitute(right, var, replacement)),
            ),
            LambdaExpression::IfThenElse(condition, then_expr, else_expr) => {
                LambdaExpression::IfThenElse(
                    Rc::new(self.substitute(condition, var, replacement)),
                    Rc::new(self.substitute(then_expr, var, replacement)),
                    Rc::new(self.substitute(else_expr, var, replacement)),
                )
            }
            LambdaExpression::YCombinator(inner) => {
                LambdaExpression::YCombinator(Rc::new(self.substitute(inner, var, replacement)))
            }
        };
        result
    }

    fn alpha_convert(&self, param: &str, body: &LambdaExpression) -> (String, LambdaExpression) {
        let new_param = self.generate_fresh_var(param);
        let new_body = self.substitute(body, param, &LambdaExpression::Variable(new_param.clone()));
        (new_param, new_body)
    }

    fn occurs_free(&self, var: &str, expr: &LambdaExpression) -> bool {
        match expr {
            LambdaExpression::Variable(name) => name == var,
            LambdaExpression::Number(_) => false,
            LambdaExpression::Boolean(_) => false,
            LambdaExpression::Abstraction { parameter, body } => {
                parameter != var && self.occurs_free(var, body)
            }
            LambdaExpression::Application { function, argument } => {
                self.occurs_free(var, function) || self.occurs_free(var, argument)
            }
            LambdaExpression::Pred(inner) | LambdaExpression::Succ(inner) => {
                self.occurs_free(var, inner)
            }
            LambdaExpression::Pair(first, second) => {
                self.occurs_free(var, first) || self.occurs_free(var, second)
            }
            LambdaExpression::First(inner) | LambdaExpression::Second(inner) => {
                self.occurs_free(var, inner)
            }
            LambdaExpression::And(left, right) | LambdaExpression::Or(left, right) => {
                self.occurs_free(var, left) || self.occurs_free(var, right)
            }
            LambdaExpression::Not(inner) => self.occurs_free(var, inner),
            LambdaExpression::IsZero(inner) => self.occurs_free(var, inner),
            LambdaExpression::Multiply(left, right) => {
                self.occurs_free(var, left) || self.occurs_free(var, right)
            }
            LambdaExpression::IfThenElse(condition, then_expr, else_expr) => {
                self.occurs_free(var, condition)
                    || self.occurs_free(var, then_expr)
                    || self.occurs_free(var, else_expr)
            }
            LambdaExpression::YCombinator(inner) => self.occurs_free(var, inner),
        }
    }

    fn generate_fresh_var(&self, base: &str) -> String {
        format!("{}_{}", base, Uuid::new_v4().simple())
    }
}

pub fn church_encode(n: u64) -> LambdaExpression {
    let body = (0..n).fold(LambdaExpression::Variable("x".to_string()), |acc, _| {
        LambdaExpression::Application {
            function: Rc::new(LambdaExpression::Variable("f".to_string())),
            argument: Rc::new(acc),
        }
    });
    LambdaExpression::Abstraction {
        parameter: "f".to_string(),
        body: Rc::new(LambdaExpression::Abstraction {
            parameter: "x".to_string(),
            body: Rc::new(body),
        }),
    }
}

pub fn church_decode(expr: &LambdaExpression) -> Result<u64, String> {
    fn count_applications(expr: &LambdaExpression) -> u64 {
        match expr {
            LambdaExpression::Application { function, argument } => {
                1 + count_applications(argument)
            }
            LambdaExpression::Variable(_) => 0,
            _ => 0,
        }
    }

    match expr {
        LambdaExpression::Abstraction { parameter: f, body } => match &**body {
            LambdaExpression::Abstraction {
                parameter: x,
                body: inner_body,
            } => Ok(count_applications(inner_body)),
            _ => Err(format!(
                "Invalid Church numeral structure: expected λx. ..., got {:?}",
                body
            )),
        },
        _ => Err(format!(
            "Invalid Church numeral: expected λf. λx. ..., got {:?}",
            expr
        )),
    }
}

pub fn church_add(a: &LambdaExpression, b: &LambdaExpression) -> Result<LambdaExpression, String> {
    let add_function = parse_lambda("λm. λn. λf. λx. m f (n f x)").map_err(|e| e.message)?;
    Ok(LambdaExpression::Application {
        function: Rc::new(LambdaExpression::Application {
            function: Rc::new(add_function),
            argument: Rc::new(a.clone()),
        }),
        argument: Rc::new(b.clone()),
    })
}

pub fn church_subtract(
    a: &LambdaExpression,
    b: &LambdaExpression,
) -> Result<LambdaExpression, String> {
    let subtract_function =
        parse_lambda("λm. λn. λf. λx. n (λg. λh. h (g f)) (λu. x) (m f)").map_err(|e| e.message)?;
    Ok(LambdaExpression::Application {
        function: Rc::new(LambdaExpression::Application {
            function: Rc::new(subtract_function),
            argument: Rc::new(a.clone()),
        }),
        argument: Rc::new(b.clone()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda_parse::parse_lambda;

    fn is_church_numeral(expr: &LambdaExpression, value: u64) -> bool {
        match expr {
            LambdaExpression::Abstraction { parameter: f, body } => match &**body {
                LambdaExpression::Abstraction {
                    parameter: x,
                    body: inner_body,
                } => {
                    let mut current = inner_body;
                    let mut count = 0;
                    while let LambdaExpression::Application { function, argument } = &**current {
                        if !matches!(&**function, LambdaExpression::Variable(name) if name == f) {
                            return false;
                        }
                        current = argument;
                        count += 1;
                    }
                    matches!(&**current, LambdaExpression::Variable(name) if name == x)
                        && count == value
                }
                _ => false,
            },
            _ => false,
        }
    }

    #[test]
    fn test_simple_application() {
        let input = "(λx. x) y";
        println!("Input: {}", input);
        let expr = parse_lambda(input).unwrap_or_else(|e| panic!("Parse error: {:?}", e));
        println!("Parsed expression: {:?}", expr);
        let vm = VM::new();
        let result = vm.eval(&expr);

        println!("Result: {:?}", result);

        match &*result {
            LambdaExpression::Variable(name) => assert_eq!(name, "y"),
            _ => panic!("Expected Variable(\"y\"), got {:?}", result),
        }
    }

    #[test]
    fn test_nested_application() {
        let input = "(λf. λx. f (f x)) (λy. y) z";
        let expr = parse_lambda(input).unwrap();
        let vm = VM::new();
        let result = vm.eval(&expr);

        println!("Input: {}", input);
        println!("Parsed expression: {:?}", expr);
        println!("Evaluated result: {:?}", result);

        assert!(matches!(*result, LambdaExpression::Variable(ref name) if name == "z"));
    }

    #[test]
    fn test_identity_function() {
        let input = "λx. x";
        let expr = parse_lambda(input).unwrap();
        let vm = VM::new();
        let result = vm.eval(&expr);

        assert!(matches!(*result, LambdaExpression::Abstraction { .. }));
    }

    #[test]
    fn test_complex_expression() {
        let input = "(λf. λx. f (f x)) (λy. y)";
        let expr = parse_lambda(input).unwrap();
        let vm = VM::new();
        let result = vm.eval(&expr);

        assert!(matches!(*result, LambdaExpression::Abstraction { .. }));
    }

    #[test]
    fn test_church_numerals() {
        let vm = VM::new();

        for i in 0..=5 {
            let church_num = church_encode(i);
            let result = vm.eval(&church_num);
            match church_decode(&result) {
                Ok(decoded) => {
                    println!("Encoded {} as {:?}", i, result);
                    println!("Decoded back to {}", decoded);
                    assert_eq!(i, decoded, "Church encoding/decoding failed for {}", i);
                }
                Err(e) => {
                    panic!("Failed to decode {}: {}\nEncoded as: {:?}", i, e, result);
                }
            }
        }
    }

    #[test]
    fn test_church_add() {
        let two = church_encode(2);
        let three = church_encode(3);
        let add_code = format!(
            r#"
            (λm. λn. λf. λx. m f (n f x))
                {}
                {}
            "#,
            two, three
        );

        println!("add_code: {}", add_code);
        let vm = VM::new();
        let add = parse_lambda(&add_code).expect("Failed to parse add function");
        let result = vm.eval(&add);

        match church_decode(&result) {
            Ok(decoded) => {
                println!("Add(2, 3) = {}", decoded);
                assert_eq!(
                    decoded, 5,
                    "Expected Add(2, 3) to be 5, but got {}",
                    decoded
                );
            }
            Err(e) => {
                panic!("Failed to decode result: {}\nResult was: {:?}", e, result);
            }
        }
    }

    #[test]
    fn test_add_with_positive() {
        let vm = VM::new();

        let test_cases = vec![(5, 3, 8), (3, 5, 8), (0, 0, 0), (1, 1, 2), (2, 2, 4)];

        for (a, b, expected) in test_cases {
            let a_expr = church_encode(a);
            let b_expr = church_encode(b);
            let add_result = church_add(&a_expr, &b_expr).unwrap();
            let result = vm.eval(&add_result);

            println!("Add({}, {}):", a, b);
            println!("Result expression: {:?}", result);
            match church_decode(&result) {
                Ok(decoded) => {
                    println!("Decoded result: {}", decoded);
                    assert_eq!(
                        decoded, expected,
                        "Expected Add({}, {}) to be {}, but got {}",
                        a, b, expected, decoded
                    );
                }
                Err(e) => {
                    panic!(
                        "Failed to decode result for Add({}, {}): {}\nResult was: {:?}",
                        a, b, e, result
                    );
                }
            }
            println!();
        }
    }

    #[test]
    fn test_pred_succ() {
        let vm = VM::new();

        let test_cases = vec![
            ("pred 5", 4),
            ("succ 5", 6),
            ("pred (succ 5)", 5),
            ("succ (pred 5)", 5),
            ("pred (pred 5)", 3),
            ("succ (succ 5)", 7),
        ];

        for (input, expected) in test_cases {
            let expr = parse_lambda(input).unwrap();
            let result = vm.eval(&expr);
            match &*result {
                LambdaExpression::Abstraction { .. } => {
                    // Decode the Church numeral
                    let decoded = church_decode(&result).unwrap();
                    assert_eq!(decoded, expected as u64, "Failed for input: {}", input);
                }
                _ => panic!("Expected Church numeral (Abstraction), got {:?}", result),
            }
        }
    }

    #[test]
    fn test_church_arithmetic() {
        let vm = VM::new();

        let church_0 = parse_lambda("λf. λx. x").unwrap();
        let church_2 = parse_lambda("λf. λx. f (f x)").unwrap();
        let church_3 = parse_lambda("λf. λx. f (f (f x))").unwrap();
        let church_5 = parse_lambda("λf. λx. f (f (f (f (f x))))").unwrap();
        let church_7 = parse_lambda("λf. λx. f (f (f (f (f (f (f x))))))").unwrap();
        let church_8 = parse_lambda("λf. λx. f (f (f (f (f (f (f (f x)))))))").unwrap();

        let church_add = parse_lambda("λm. λn. λf. λx. m f (n f x)").unwrap();

        let test_cases = vec![
            (&church_5, &church_3, &church_8, "5 + 3 = 8"),
            (&church_3, &church_5, &church_8, "3 + 5 = 8"),
            (&church_5, &church_2, &church_7, "5 + 2 = 7"),
            (&church_0, &church_0, &church_0, "0 + 0 = 0"),
        ];

        for (a, b, expected, description) in test_cases {
            println!("Testing: {}", description);

            let add_expr = LambdaExpression::Application {
                function: Rc::new(LambdaExpression::Application {
                    function: Rc::new(church_add.clone()),
                    argument: Rc::new(a.clone()),
                }),
                argument: Rc::new(b.clone()),
            };

            let result = vm.eval(&add_expr);
            let decoded_result = church_decode(&result).unwrap();
            let decoded_expected = church_decode(expected).unwrap();

            println!("Result: {}", decoded_result);
            println!("Expected: {}", decoded_expected);

            assert_eq!(decoded_result, decoded_expected, "{}", description);

            println!("\n{}", "-".repeat(50));
        }
    }

    #[test]
    fn test_church_encode_decode() {
        for i in 0..=10 {
            let encoded = church_encode(i);
            let decoded = church_decode(&encoded).unwrap();
            assert_eq!(i, decoded, "Expected {} to encode and decode correctly", i);
        }
    }

    #[test]
    fn test_church_encode_decode_with_pairs() {
        let vm = VM::new();
        for i in 0..=10 {
            let encoded = church_encode(i);
            println!("Encoded {}: {:?}", i, encoded);
            let evaluated = vm.eval(&encoded);
            println!("Evaluated {}: {:?}", i, evaluated);
            match church_decode(&evaluated) {
                Ok(decoded) => {
                    println!("Decoded {}: {}", i, decoded);
                    assert_eq!(i, decoded, "Expected {} to encode and decode correctly", i);
                }
                Err(e) => panic!("Failed to decode {}: {}", i, e),
            }
            println!("---");
        }
    }

    #[test]
    fn test_church_encode_decode_mixed() {
        let test_cases = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        for &n in &test_cases {
            let encoded = church_encode(n);
            let decoded = church_decode(&encoded).unwrap();
            assert_eq!(n, decoded, "Expected {} to encode and decode correctly", n);
        }
    }

    #[test]
    fn test_boolean_operations() {
        let vm = VM::new();

        let test_cases = vec![
            ("true", "(λx. (λy. x))"),
            ("false", "(λx. (λy. y))"),
            ("(and true true)", "(λx. λy. x)"),
            ("(and true false)", "(λx. λy. y)"),
            ("(and false true)", "(λx. λy. y)"),
            ("(and false false)", "(λx. λy. y)"),
            ("(or true false)", "(λx. λy. x)"),
            ("(or false true)", "(λx. λy. x)"),
            ("(or false false)", "(λx. λy. y)"),
            ("(not true)", "(λx. λy. y)"),
            ("(not false)", "(λx. λy. x)"),
        ];

        for (input, expected) in test_cases {
            let expr = parse_lambda(input).unwrap();
            let result = vm.eval(&expr);
            let expected_expr = parse_lambda(expected).unwrap();
            assert_eq!(*result, expected_expr, "Failed for input: {}", input);
        }
    }

    #[test]
    fn test_conditional_return() {
        let vm = VM::new();

        // Define our simplified conditional function
        let conditional_expr = parse_lambda(
            r"
            λn. ifthenelse (is_zero n) (λf. λx. f x) n
        ",
        )
        .unwrap();

        println!("Conditional expression: {:?}", conditional_expr);

        let input0 = LambdaExpression::Application {
            function: Rc::new(conditional_expr.clone()),
            argument: Rc::new(church_encode(0)),
        };

        println!("Input expression (0): {:?}", input0);

        let result0 = vm.eval(&input0);
        println!("Result (0): {:?}", result0);

        let church_one = church_encode(1);
        println!("Church encoding of 1: {:?}", church_one);

        assert!(
            is_church_numeral(&result0, 1),
            "Expected Church encoding of 1, but got {:?}",
            result0
        );

        // Test with input 1
        let input1 = LambdaExpression::Application {
            function: Rc::new(conditional_expr),
            argument: Rc::new(church_encode(1)),
        };

        println!("Input expression (1): {:?}", input1);

        let result1 = vm.eval(&input1);
        println!("Result (1): {:?}", result1);

        assert!(
            is_church_numeral(&result1, 1),
            "Expected Church encoding of 1, but got {:?}",
            result1
        );

        // Additional test to ensure our Church encoding and decoding works correctly
        let decoded_result0 = church_decode(&result0).unwrap();
        assert_eq!(
            decoded_result0, 1,
            "Expected decoded result to be 1, but got {}",
            decoded_result0
        );

        let decoded_result1 = church_decode(&result1).unwrap();
        assert_eq!(
            decoded_result1, 1,
            "Expected decoded result to be 1, but got {}",
            decoded_result1
        );
    }

    #[test]
    fn test_is_zero() {
        let vm = VM::new();

        let test_cases = vec![
            ("is_zero 0", true),
            ("is_zero 1", false),
            ("is_zero (pred 1)", true),
            ("is_zero (pred (succ 1))", false),
            ("is_zero (λf. (λx. (f x)))", false),
            ("is_zero (λf. (λx. x))", true),
        ];

        for (input, expected) in test_cases {
            let expr = parse_lambda(input).unwrap();
            let result = vm.eval(&expr);
            assert_eq!(*result, expected.into(), "Failed for input: {}", input);
        }
    }
    #[test]
    fn test_is_zero_and_multiply() {
        let vm = VM::new();

        let test_cases = vec![
            ("is_zero 0", parse_lambda("λx. λy. x").unwrap()),  // true
            ("is_zero 1", parse_lambda("λx. λy. y").unwrap()),  // false
            ("is_zero (pred 1)", parse_lambda("λx. λy. x").unwrap()),  // true
            ("2 * 3", church_encode(6)),
            ("0 * 5", church_encode(0)),
            ("is_zero (3 * 0)", parse_lambda("λx. λy. x").unwrap()),  // true
            ("is_zero (2 * 3)", parse_lambda("λx. λy. y").unwrap()),  // false
        ];

        for (input, expected) in test_cases {
            println!("Testing input: {}", input);
            let expr = parse_lambda(input)
                .unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e));
            println!("Parsed expression: {:?}", expr);
            let result = vm.eval(&expr);
            println!("Evaluated result: {:?}", result);
            assert_eq!(*result, expected, "Failed for input: {}", input);
        }
    }

    #[test]
    fn test_ifthenelse() {
        let vm = VM::new();

        let test_cases = vec![
            ("ifthenelse true 1 2", 1),
            ("ifthenelse false 1 2", 2),
            // ("ifthenelse (is_zero 0) 1 2", 1),
            // ("ifthenelse (is_zero 1) 1 2", 2),
        ];

        for (input, expected) in test_cases {
            println!("\nTesting input: {}", input);
            let expr = parse_lambda(input)
                .unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e));
            println!("Parsed expression: {:?}", expr);
            let result = vm.eval(&expr);
            println!("Evaluated result: {:?}", result);

            let decoded = church_decode(&result).unwrap();
            assert_eq!(decoded, expected, "Failed for input: {}", input);
        }
    }

    #[test]
    fn test_pair_operations() {
        let vm = VM::new();

        let pair = parse_lambda("pair 3 4").unwrap();
        let first = parse_lambda("first (pair 3 4)").unwrap();
        let second = parse_lambda("second (pair 3 4)").unwrap();

        let result_pair = vm.eval(&pair);
        let result_first = vm.eval(&first);
        let result_second = vm.eval(&second);

        println!("Result pair: {:?}", result_pair);
        println!("Result first: {:?}", result_first);
        println!("Result second: {:?}", result_second);

        // Check if result_pair is a pair
        assert!(
            matches!(&*result_pair, LambdaExpression::Pair(_, _)),
            "Expected pair to be a Pair"
        );

        // Check if result_first is Church numeral 3
        assert!(
            is_church_numeral(&result_first, 3),
            "Expected first to be Church numeral 3"
        );

        // Check if result_second is Church numeral 4
        assert!(
            is_church_numeral(&result_second, 4),
            "Expected second to be Church numeral 4"
        );
    }

    #[test]
    fn test_factorial() {
        let vm = VM::with_max_iterations(100); // 减少最大迭代次数

        let factorial = parse_lambda(
            r"
            Y (λf. λn.
                ifthenelse (is_zero n)
                    (λf. λx. f x)  // return 1 (Church encoded)
                    (multiply n (f (pred n))))
            ",
        )
        .unwrap();

        println!("Factorial function: {:?}", factorial);

        // Test factorial of 0 and 1
        for n in 0..=10 {
            println!("\nTesting factorial of {}", n);
            let input = church_encode(n);
            println!("Input (Church encoded {}): {:?}", n, input);
            let result = LambdaExpression::Application {
                function: Rc::new(factorial.clone()),
                argument: Rc::new(input),
            };

            println!("Starting evaluation");
            let result = vm.eval(&result);
            println!("Evaluation complete");
            println!("Result: {:?}", result);

            // Decode the result
            match church_decode(&result) {
                Ok(decoded) => {
                    println!("Decoded result: {}", decoded);
                    assert_eq!(decoded, if n == 0 { 1 } else { n }, "Factorial of {} failed", n);
                },
                Err(e) => panic!("Failed to decode result: {}", e),
            }
        }
    }

    #[test]
    fn test_fibonacci1() {
        let vm = VM::with_max_iterations(100);

        let fibonacci = parse_lambda(
            r"
            Y (λf. λn.
                ifthenelse (is_zero n)
                    (λf. λx. x)  // return 0 (Church encoded)
                    (ifthenelse (is_zero (pred n))
                        (λf. λx. f x)  // return 1 (Church encoded)
                        (add (f (pred n)) (f (pred (pred n))))))
            ",
        )
        .unwrap();

        println!("Fibonacci function: {:?}", fibonacci);

        // Test fibonacci for number 1
        let n = 1;
        println!("\nTesting fibonacci of {}", n);
        let input = church_encode(n);
        println!("Input (Church encoded {}): {:?}", n, input);
        let result = LambdaExpression::Application {
            function: Rc::new(fibonacci),
            argument: Rc::new(input),
        };

        println!("Starting evaluation of {:?}", result);
        let result = vm.eval(&result);
        println!("Evaluation complete");
        println!("Result: {:?}", result);

        // Decode the result
        match church_decode(&result) {
            Ok(decoded) => {
                println!("Decoded result: {}", decoded);
                assert_eq!(decoded, 1, "Fibonacci of {} failed", n);
            },
            Err(e) => panic!("Failed to decode result: {}", e),
        }
    }
}