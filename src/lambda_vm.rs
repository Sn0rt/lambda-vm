use std::rc::Rc;
use std::collections::HashMap;
use crate::lambda_parse::LambdaExpression;

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

pub struct VM;

impl VM {
    pub fn new() -> Self {
        VM
    }

    pub fn eval(&self, expr: &LambdaExpression) -> Rc<LambdaExpression> {
        match expr {
            LambdaExpression::Variable(_) => Rc::new(expr.clone()),
            LambdaExpression::Number(_) => Rc::new(expr.clone()),
            LambdaExpression::Abstraction { parameter, body } => {
                Rc::new(LambdaExpression::Abstraction {
                    parameter: parameter.clone(),
                    body: body.clone(),
                })
            },
            LambdaExpression::Application { function, argument } => {
                let func = self.eval(function);
                
                match &*func {
                    LambdaExpression::Abstraction { parameter, body } => {
                        let arg = self.eval(argument);
                        let result = self.substitute(body, parameter, &arg);
                        self.eval(&result)
                    }
                    _ => {
                        let arg = self.eval(argument);
                        Rc::new(LambdaExpression::Application {
                            function: func,
                            argument: arg,
                        })
                    }
                }
            }
        }
    }

    fn substitute(&self, expr: &LambdaExpression, var: &str, replacement: &LambdaExpression) -> LambdaExpression {
        match expr {
            LambdaExpression::Variable(name) if name == var => replacement.clone(),
            LambdaExpression::Variable(_) => expr.clone(),
            LambdaExpression::Number(_) => expr.clone(), // 新增：处理 Number 变体
            LambdaExpression::Abstraction { parameter, body } => {
                if parameter == var {
                    expr.clone()
                } else {
                    let new_body = self.substitute(body, var, replacement);
                    LambdaExpression::Abstraction {
                        parameter: parameter.clone(),
                        body: Rc::new(new_body),
                    }
                }
            }
            LambdaExpression::Application { function, argument } => {
                LambdaExpression::Application {
                    function: Rc::new(self.substitute(function, var, replacement)),
                    argument: Rc::new(self.substitute(argument, var, replacement)),
                }
            }
        }
    }

    fn alpha_convert(&self, param: &str, body: &LambdaExpression, _var: &str, replacement: &LambdaExpression) -> (String, LambdaExpression) {
        if self.occurs_free(param, replacement) {
            let new_param = self.generate_fresh_var(param);
            let new_body = self.substitute(body, param, &LambdaExpression::Variable(new_param.clone()));
            (new_param, new_body)
        } else {
            (param.to_string(), body.clone())
        }
    }

    fn occurs_free(&self, var: &str, expr: &LambdaExpression) -> bool {
        match expr {
            LambdaExpression::Variable(name) => name == var,
            LambdaExpression::Number(_) => false, // 新增：数字中不会出现自由变量
            LambdaExpression::Abstraction { parameter, body } => {
                parameter != var && self.occurs_free(var, body)
            }
            LambdaExpression::Application { function, argument } => {
                self.occurs_free(var, function) || self.occurs_free(var, argument)
            }
        }
    }

    fn generate_fresh_var(&self, base: &str) -> String {
        format!("{}'", base)
    }
}

// 添加一些辅助函数来实现自然数的 Church 编码
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

pub fn church_decode(expr: &LambdaExpression) -> Option<u64> {
    match expr {
        LambdaExpression::Abstraction { parameter: f, body } => {
            match &**body {
                LambdaExpression::Abstraction { parameter: x, body: inner_body } => {
                    church_decode_helper(inner_body, f, x)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn church_decode_helper(expr: &LambdaExpression, f: &str, x: &str) -> Option<u64> {
    match expr {
        LambdaExpression::Variable(var) if var == x => Some(0),
        LambdaExpression::Application { function, argument } => {
            if let LambdaExpression::Variable(var) = &**function {
                if var == f {
                    church_decode_helper(argument, f, x).map(|n| n + 1)
                } else {
                    None
                }
            } else {
                None
            }
        }
        _ => None,
    }
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

        // Test church encoding and decoding
        for i in 0..10 {
            let church_num = church_encode(i);
            let result = vm.eval(&church_num);
            let decoded = church_decode(&result).unwrap();
            assert_eq!(i, decoded);
        }
    }

    #[test]
    fn test_fibonacci() {
        let fib_code = r#"
            (λfib. λn.
                ((λf. λx. f (f x))
                 (λf. λg. λn. 
                    (λlte. λa. λb. 
                        lte n (λx. λy. y)
                            a
                            (λx. g f g (λf. λx. f (f x)) n a b)
                    )
                    (λm. λn. λt. λf. m (λx. n t (λx. f)) t)
                    (λf. λx. f x)
                    (λf. λx. f (f x))
                )
                (λf. λg. λn. 
                    (λlte. λa. λb. 
                        lte n (λx. λy. y)
                            a
                            (λx. g f g (λf. λx. f (f x)) n a b)
                    )
                    (λm. λn. λt. λf. m (λx. n t (λx. f)) t)
                    (λf. λx. f x)
                    (λf. λx. f (f x))
                )
                n
            )
        "#;

        let fib = parse_lambda(fib_code).unwrap();
        let vm = VM::new();

        for i in 0..10 {
            let input = LambdaExpression::Application {
                function: Rc::new(fib.clone()),
                argument: Rc::new(church_encode(i)),
            };
            let result = vm.eval(&input);
            let decoded = church_decode(&result).unwrap();
            
            // Calculate expected Fibonacci number
            let expected = match i {
                0 | 1 => i,
                _ => {
                    let mut a = 0;
                    let mut b = 1;
                    for _ in 2..=i {
                        let temp = a + b;
                        a = b;
                        b = temp;
                    }
                    b
                }
            };

            assert_eq!(decoded, expected, "Fibonacci({}) should be {}", i, expected);
        }
    }
}