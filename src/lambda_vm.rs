use crate::lambda_parse::{LambdaExpression, parse_lambda};
use std::rc::Rc;
use std::collections::HashMap;
use uuid::Uuid;

#[derive(Clone)]
pub struct Environment {
    bindings: HashMap<String, Rc<LambdaExpression>>,
    parent: Option<Rc<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            bindings: HashMap::new(),
            parent: None,
        }
    }

    pub fn extend(parent: Rc<Environment>) -> Self {
        Environment {
            bindings: HashMap::new(),
            parent: Some(parent),
        }
    }

    pub fn get(&self, name: &str) -> Option<Rc<LambdaExpression>> {
        self.bindings.get(name).cloned().or_else(|| {
            self.parent.as_ref().and_then(|p| p.get(name))
        })
    }

    pub fn set(&mut self, name: String, value: Rc<LambdaExpression>) {
        self.bindings.insert(name, value);
    }
}

pub struct VM {
    max_iterations: usize,
}

impl VM {
    pub fn new() -> Self {
        VM {
            max_iterations: 1000000, // 默认值
        }
    }

    pub fn with_max_iterations(max_iterations: usize) -> Self {
        VM {
            max_iterations,
        }
    }

    pub fn eval(&self, expr: &LambdaExpression) -> Rc<LambdaExpression> {
        let mut current_expr = Rc::new(expr.clone());
        for i in 0..self.max_iterations {
            let new_expr = self.eval_step(&current_expr);
            if *new_expr == *current_expr {
                println!("Evaluation completed after {} iterations", i);
                return new_expr;
            }
            current_expr = new_expr;
        }
        println!("Warning: Reached maximum iterations ({}). Expression may not be fully evaluated.", self.max_iterations);
        current_expr
    }

    fn eval_step(&self, expr: &LambdaExpression) -> Rc<LambdaExpression> {
        println!("Evaluating: {:?}", expr);
        match expr {
            LambdaExpression::Variable(_) | LambdaExpression::Number(_) => Rc::new(expr.clone()),
            LambdaExpression::Abstraction { parameter, body } => {
                let eval_body = self.eval_step(body);
                if *eval_body == **body {
                    Rc::new(expr.clone())
                } else {
                    Rc::new(LambdaExpression::Abstraction {
                        parameter: parameter.clone(),
                        body: eval_body,
                    })
                }
            },
            LambdaExpression::Application { function, argument } => {
                let eval_func = self.eval_step(function);
                match &*eval_func {
                    LambdaExpression::Abstraction { parameter, body } => {
                        let eval_arg = self.eval_step(argument);
                        let substituted = self.substitute(body, parameter, &eval_arg);
                        self.eval_step(&substituted)
                    }
                    _ => {
                        let eval_arg = self.eval_step(argument);
                        Rc::new(LambdaExpression::Application {
                            function: eval_func,
                            argument: eval_arg,
                        })
                    }
                }
            },
            LambdaExpression::Pred(inner) => {
                let eval_inner = self.eval_step(inner);
                match &*eval_inner {
                    LambdaExpression::Number(n) => Rc::new(LambdaExpression::Number(n.saturating_sub(1))),
                    _ => Rc::new(LambdaExpression::Pred(eval_inner)),
                }
            },
            LambdaExpression::Succ(inner) => {
                let eval_inner = self.eval_step(inner);
                match &*eval_inner {
                    LambdaExpression::Number(n) => Rc::new(LambdaExpression::Number(n + 1)),
                    _ => Rc::new(LambdaExpression::Succ(eval_inner)),
                }
            },
            LambdaExpression::Pair(first, second) => {
                let eval_first = self.eval_step(first);
                let eval_second = self.eval_step(second);
                if Rc::ptr_eq(&eval_first, first) && Rc::ptr_eq(&eval_second, second) {
                    Rc::new(expr.clone())
                } else {
                    Rc::new(LambdaExpression::Pair(eval_first, eval_second))
                }
            },
            LambdaExpression::First(inner) => {
                let eval_inner = self.eval_step(inner);
                match &*eval_inner {
                    LambdaExpression::Pair(first, _) => first.clone(),
                    _ => Rc::new(LambdaExpression::First(eval_inner)),
                }
            },
            LambdaExpression::Second(inner) => {
                let eval_inner = self.eval_step(inner);
                match &*eval_inner {
                    LambdaExpression::Pair(_, second) => second.clone(),
                    _ => Rc::new(LambdaExpression::Second(eval_inner)),
                }
            },
            LambdaExpression::Boolean(_) => Rc::new(expr.clone()),
            LambdaExpression::And(left, right) => {
                let eval_left = self.eval_step(left);
                let eval_right = self.eval_step(right);
                match (&*eval_left, &*eval_right) {
                    (LambdaExpression::Abstraction { .. }, LambdaExpression::Abstraction { .. }) => {
                        let and_expr = parse_lambda("λp. λq. p q p").unwrap();
                        let applied = LambdaExpression::Application {
                            function: Rc::new(LambdaExpression::Application {
                                function: Rc::new(and_expr),
                                argument: eval_left,
                            }),
                            argument: eval_right,
                        };
                        self.eval_step(&applied)
                    },
                    _ => Rc::new(LambdaExpression::And(eval_left, eval_right)),
                }
            },
            LambdaExpression::Or(left, right) => {
                let eval_left = self.eval_step(left);
                let eval_right = self.eval_step(right);
                match (&*eval_left, &*eval_right) {
                    (LambdaExpression::Abstraction { .. }, LambdaExpression::Abstraction { .. }) => {
                        let or_expr = parse_lambda("λp. λq. p p q").unwrap();
                        let applied = LambdaExpression::Application {
                            function: Rc::new(LambdaExpression::Application {
                                function: Rc::new(or_expr),
                                argument: eval_left,
                            }),
                            argument: eval_right,
                        };
                        self.eval_step(&applied)
                    },
                    _ => Rc::new(LambdaExpression::Or(eval_left, eval_right)),
                }
            },
            LambdaExpression::Not(inner) => {
                let eval_inner = self.eval_step(inner);
                match &*eval_inner {
                    LambdaExpression::Abstraction { .. } => {
                        let not_expr = parse_lambda("λp. p (λx. λy. y) (λx. λy. x)").unwrap();
                        let applied = LambdaExpression::Application {
                            function: Rc::new(not_expr),
                            argument: eval_inner,
                        };
                        self.eval_step(&applied)
                    },
                    _ => Rc::new(LambdaExpression::Not(eval_inner)),
                }
            },
            LambdaExpression::IsZero(inner) => {
                let eval_inner = self.eval_step(inner);
                match &*eval_inner {
                    LambdaExpression::Number(n) => Rc::new(LambdaExpression::Boolean(*n == 0)),
                    _ => Rc::new(LambdaExpression::IsZero(eval_inner)),
                }
            },
            LambdaExpression::Multiply(left, right) => {
                let eval_left = self.eval_step(left);
                let eval_right = self.eval_step(right);
                match (&*eval_left, &*eval_right) {
                    (LambdaExpression::Number(l), LambdaExpression::Number(r)) => {
                        Rc::new(LambdaExpression::Number(l * r))
                    },
                    _ => Rc::new(LambdaExpression::Multiply(eval_left, eval_right)),
                }
            },
            LambdaExpression::IfThenElse(condition, then_expr, else_expr) => {
                let eval_condition = self.eval(condition); // 完全归约条件
                match &*eval_condition {
                    LambdaExpression::Abstraction { parameter: x, body } => {
                        match &**body {
                            LambdaExpression::Abstraction { parameter: y, body: inner_body } => {
                                match &**inner_body {
                                    LambdaExpression::Variable(name) if name == x => {
                                        // This is true (λx.λy.x)
                                        self.eval(then_expr)
                                    },
                                    LambdaExpression::Variable(name) if name == y => {
                                        // This is false (λx.λy.y)
                                        self.eval(else_expr)
                                    },
                                    _ => Rc::new(LambdaExpression::IfThenElse(
                                        eval_condition,
                                        Rc::clone(then_expr),
                                        Rc::clone(else_expr)
                                    )),
                                }
                            },
                            _ => Rc::new(LambdaExpression::IfThenElse(
                                eval_condition,
                                Rc::clone(then_expr),
                                Rc::clone(else_expr)
                            )),
                        }
                    },
                    LambdaExpression::Boolean(true) => self.eval(then_expr),
                    LambdaExpression::Boolean(false) => self.eval(else_expr),
                    _ => Rc::new(LambdaExpression::IfThenElse(
                        eval_condition,
                        Rc::clone(then_expr),
                        Rc::clone(else_expr)
                    )),
                }
            },
            LambdaExpression::YCombinator(f) => {
                let eval_f = self.eval_step(f);
                match &*eval_f {
                    LambdaExpression::Abstraction { parameter, body } => {
                        let y_applied = LambdaExpression::Application {
                            function: Rc::new(LambdaExpression::YCombinator(eval_f.clone())),
                            argument: eval_f.clone(),
                        };
                        let substituted = self.substitute(body, parameter, &y_applied);
                        self.eval_step(&substituted)
                    }
                    _ => {
                        Rc::new(LambdaExpression::YCombinator(eval_f))
                    }
                }
            },
        }
    }

    fn substitute(&self, expr: &LambdaExpression, var: &str, replacement: &LambdaExpression) -> LambdaExpression {
        println!("Substituting {} with {:?} in {:?}", var, replacement, expr);
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
            LambdaExpression::Application { function, argument } => {
                LambdaExpression::Application {
                    function: Rc::new(self.substitute(function, var, replacement)),
                    argument: Rc::new(self.substitute(argument, var, replacement)),
                }
            }
            LambdaExpression::Pred(inner) => {
                LambdaExpression::Pred(Rc::new(self.substitute(inner, var, replacement)))
            }
            LambdaExpression::Succ(inner) => {
                LambdaExpression::Succ(Rc::new(self.substitute(inner, var, replacement)))
            }
            LambdaExpression::Pair(first, second) => {
                LambdaExpression::Pair(
                    Rc::new(self.substitute(first, var, replacement)),
                    Rc::new(self.substitute(second, var, replacement))
                )
            },
            LambdaExpression::First(inner) => {
                LambdaExpression::First(Rc::new(self.substitute(inner, var, replacement)))
            },
            LambdaExpression::Second(inner) => {
                LambdaExpression::Second(Rc::new(self.substitute(inner, var, replacement)))
            },
            LambdaExpression::And(left, right) => {
                LambdaExpression::And(
                    Rc::new(self.substitute(left, var, replacement)),
                    Rc::new(self.substitute(right, var, replacement))
                )
            },
            LambdaExpression::Or(left, right) => {
                LambdaExpression::Or(
                    Rc::new(self.substitute(left, var, replacement)),
                    Rc::new(self.substitute(right, var, replacement))
                )
            },
            LambdaExpression::Not(inner) => {
                LambdaExpression::Not(Rc::new(self.substitute(inner, var, replacement)))
            },
            LambdaExpression::IsZero(inner) => {
                LambdaExpression::IsZero(Rc::new(self.substitute(inner, var, replacement)))
            },
            LambdaExpression::Multiply(left, right) => {
                LambdaExpression::Multiply(
                    Rc::new(self.substitute(left, var, replacement)),
                    Rc::new(self.substitute(right, var, replacement))
                )
            },
            LambdaExpression::IfThenElse(condition, then_expr, else_expr) => {
                LambdaExpression::IfThenElse(
                    Rc::new(self.substitute(condition, var, replacement)),
                    Rc::new(self.substitute(then_expr, var, replacement)),
                    Rc::new(self.substitute(else_expr, var, replacement))
                )
            },
            LambdaExpression::YCombinator(inner) => {
                LambdaExpression::YCombinator(Rc::new(self.substitute(inner, var, replacement)))
            },
        };
        println!("Substitution result: {:?}", result);
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
            },
            LambdaExpression::First(inner) | LambdaExpression::Second(inner) => {
                self.occurs_free(var, inner)
            },
            LambdaExpression::And(left, right) | LambdaExpression::Or(left, right) => {
                self.occurs_free(var, left) || self.occurs_free(var, right)
            },
            LambdaExpression::Not(inner) => {
                self.occurs_free(var, inner)
            },
            LambdaExpression::IsZero(inner) => self.occurs_free(var, inner),
            LambdaExpression::Multiply(left, right) => {
                self.occurs_free(var, left) || self.occurs_free(var, right)
            },
            LambdaExpression::IfThenElse(condition, then_expr, else_expr) => {
                self.occurs_free(var, condition) ||
                self.occurs_free(var, then_expr) ||
                self.occurs_free(var, else_expr)
            },
            LambdaExpression::YCombinator(inner) => {
                self.occurs_free(var, inner)
            },
        }
    }

    fn generate_fresh_var(&self, base: &str) -> String {
        format!("{}_{}", base, Uuid::new_v4().simple())
    }
}

// 添加一些辅函数来实现自然的 Church 编码
pub fn church_encode(n: u64) -> LambdaExpression {
    LambdaExpression::Abstraction {
        parameter: "f".to_string(),
        body: Rc::new(LambdaExpression::Abstraction {
            parameter: "x".to_string(),
            body: Rc::new(church_encode_helper(n)),
        }),
    }
}

fn church_encode_helper(n: u64) -> LambdaExpression {
    if n == 0 {
        LambdaExpression::Variable("x".to_string())
    } else {
        LambdaExpression::Application {
            function: Rc::new(LambdaExpression::Variable("f".to_string())),
            argument: Rc::new(church_encode_helper(n - 1)),
        }
    }
}

pub fn church_decode(expr: &LambdaExpression) -> Result<u64, String> {
    fn count_applications(expr: &LambdaExpression) -> u64 {
        match expr {
            LambdaExpression::Application { function, argument } => {
                match &**function {
                    LambdaExpression::Variable(_) => 1 + count_applications(argument),
                    _ => count_applications(function) + count_applications(argument),
                }
            }
            LambdaExpression::Variable(_) => 0,
            _ => 0,
        }
    }

    match expr {
        LambdaExpression::Abstraction { parameter: _f, body } => {
            match &**body {
                LambdaExpression::Abstraction { parameter: _x, body: inner_body } => {
                    Ok(count_applications(inner_body))
                }
                _ => Err("Invalid Church numeral structure: expected λx. ...".to_string()),
            }
        }
        _ => Err("Invalid Church numeral: expected λf. λx. ...".to_string()),
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

pub fn church_subtract(a: &LambdaExpression, b: &LambdaExpression) -> Result<LambdaExpression, String> {
    let subtract_function = parse_lambda("λm. λn. λf. λx. n (λg. λh. h (g f)) (λu. x) (m f)").map_err(|e| e.message)?;
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
                },
                Err(e) => {
                    panic!("Failed to decode {}: {}\nEncoded as: {:?}", i, e, result);
                }
            }
        }
    }

    #[test]
    fn test_church_add() {
        // 2 + 3 = 5
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
                assert_eq!(decoded, 5, "Expected Add(2, 3) to be 5, but got {}", decoded);
            },
            Err(e) => {
                panic!("Failed to decode result: {}\nResult was: {:?}", e, result);
            }
        }
    }

    #[test]
    fn test_add_with_positive() {
        let vm = VM::new();

        let test_cases = vec![
            (5, 3, 8),
            (3, 5, 8),
            (0, 0, 0),
            (1, 1, 2),
            (2, 2, 4),
        ];

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
                    assert_eq!(decoded, expected, "Expected Add({}, {}) to be {}, but got {}", a, b, expected, decoded);
                },
                Err(e) => {
                    panic!("Failed to decode result for Add({}, {}): {}\nResult was: {:?}", a, b, e, result);
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
                LambdaExpression::Number(n) => assert_eq!(*n, expected),
                _ => panic!("Expected Number, got {:?}", result),
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
                },
                Err(e) => panic!("Failed to decode {}: {}", i, e),
            }
            println!("---");
        }
    }

    #[test]
    fn test_church_encode_decode_mixed() {
        let test_cases = vec![
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10
        ];

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
            ("(and true true)", "(λx. (λy. x))"),
            ("(and true false)", "(λx. (λy. y))"),
            ("(and false true)", "(λx. (λy. y))"),
            ("(and false false)", "(λx. (λy. y))"),
            ("(or true false)", "(λx. (λy. x))"),
            ("(or false true)", "(λx. (λy. x))"),
            ("(or false false)", "(λx. (λy. y))"),
            ("(not true)", "(λx. (λy. y))"),
            ("(not false)", "(λx. (λy. x))"),
        ];

        for (input, expected) in test_cases {
            let expr = parse_lambda(input).unwrap();
            let result = vm.eval(&expr);
            let expected_expr = parse_lambda(expected).unwrap();
            assert_eq!(*result, expected_expr, "Failed for input: {}", input);
        }
    }

    #[test]
    fn test_factorial3() {
        let vm = VM::new();

        // Factorial function using Y combinator
        let factorial = parse_lambda(r"
            Y (λf. λn.
                ifthenelse (is_zero n)
                    1
                    (multiply n (f (pred n))))
        ").unwrap();

        println!("Factorial function: {:?}", factorial);

        let three = church_encode(3);
        println!("Church encoding of 3: {:?}", three);

        let expr = LambdaExpression::Application {
            function: Rc::new(factorial),
            argument: Rc::new(three),
        };

        println!("Expression to evaluate: {:?}", expr);

        let result = vm.eval(&expr);
        println!("Factorial result: {:?}", result);

        match church_decode(&result) {
            Ok(decoded) => {
                println!("Factorial(3) = {}", decoded);
                assert_eq!(decoded, 6, "Expected Factorial(3) to be 6, but got {}", decoded);
            },
            Err(e) => {
                panic!("Failed to decode result: {}\nResult was: {:?}", e, result);
            }
        }
    }

    #[test]
    fn test_is_zero_and_multiply() {
        let vm = VM::new();

        let test_cases = vec![
            ("is_zero 0", LambdaExpression::Boolean(true)),
            ("is_zero 1", LambdaExpression::Boolean(false)),
            ("is_zero (pred 1)", LambdaExpression::Boolean(true)),
            ("2 * 3", LambdaExpression::Number(6)),
            ("0 * 5", LambdaExpression::Number(0)),
            ("is_zero (3 * 0)", LambdaExpression::Boolean(true)),
            ("is_zero (2 * 3)", LambdaExpression::Boolean(false)),
        ];

        for (input, expected) in test_cases {
            println!("Testing input: {}", input);
            let expr = parse_lambda(input).unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e));
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
            ("ifthenelse true 42 58", LambdaExpression::Number(42)),
            ("ifthenelse false 42 58", LambdaExpression::Number(58)),
            ("ifthenelse (is_zero 0) 42 58", LambdaExpression::Number(42)),
            ("ifthenelse (is_zero 1) 42 58", LambdaExpression::Number(58)),
        ];

        for (input, expected) in test_cases {
            println!("\nTesting input: {}", input);
            let expr = parse_lambda(input).unwrap_or_else(|e| panic!("Failed to parse '{}': {:?}", input, e));
            println!("Parsed expression: {:?}", expr);
            let result = vm.eval(&expr);
            println!("Evaluated result: {:?}", result);
            assert_eq!(*result, expected, "Failed for input: {}", input);
        }
    }

    #[test]
    fn test_pair_operations() {
        let vm = VM::new();

        let pair = parse_lambda("(pair 3 4)").unwrap();
        let first = parse_lambda("(first (pair 3 4))").unwrap();
        let second = parse_lambda("(second (pair 3 4))").unwrap();

        let result_pair = vm.eval(&pair);
        let result_first = vm.eval(&first);
        let result_second = vm.eval(&second);

        assert!(matches!(&*result_pair, LambdaExpression::Pair(first, second)
            if matches!(&**first, LambdaExpression::Number(3))
            && matches!(&**second, LambdaExpression::Number(4))));
        assert!(matches!(&*result_first, LambdaExpression::Number(3)));
        assert!(matches!(&*result_second, LambdaExpression::Number(4)));
    }
}