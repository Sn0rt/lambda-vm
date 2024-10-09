use std::rc::Rc;
use std::iter::Peekable;
use std::vec::IntoIter;
use std::fmt;

// <expression>  :== <abstraction> | <application> | <variable>
// <abstraction> :== λ <variable> . <expression>
// <application> :== ( <expression> <expression> )
// <variable>    :== v1 | v2 | ...

#[derive(Clone, PartialEq)]
pub enum LambdaExpression {
    Variable(String),
    Abstraction {
        parameter: String,
        body: Rc<LambdaExpression>,
    },
    Application {
        function: Rc<LambdaExpression>,
        argument: Rc<LambdaExpression>,
    },
    Number(i64),
    Pred(Rc<LambdaExpression>),
    Succ(Rc<LambdaExpression>),
    Pair(Rc<LambdaExpression>, Rc<LambdaExpression>),
    Fst(Rc<LambdaExpression>),
    Snd(Rc<LambdaExpression>),
    Boolean(bool),
    And(Rc<LambdaExpression>, Rc<LambdaExpression>),
    Or(Rc<LambdaExpression>, Rc<LambdaExpression>),
    Not(Rc<LambdaExpression>),
    IsZero(Rc<LambdaExpression>),
    Multiply(Rc<LambdaExpression>, Rc<LambdaExpression>),
    IfElse(Rc<LambdaExpression>, Rc<LambdaExpression>, Rc<LambdaExpression>),
}

impl fmt::Debug for LambdaExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for LambdaExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LambdaExpression::Variable(name) => write!(f, "{}", name),
            LambdaExpression::Abstraction { parameter, body } => write!(f, "(λ{}. {})", parameter, body),
            LambdaExpression::Application { function, argument } => write!(f, "({} {})", function, argument),
            LambdaExpression::Number(n) => write!(f, "{}", n),
            LambdaExpression::Pred(expr) => write!(f, "(pred {})", expr),
            LambdaExpression::Succ(expr) => write!(f, "(succ {})", expr),
            LambdaExpression::Pair(first, second) => write!(f, "(pair {} {})", first, second), // 新增
            LambdaExpression::Fst(expr) => write!(f, "(fst {})", expr),
            LambdaExpression::Snd(expr) => write!(f, "(snd {})", expr),
            LambdaExpression::Boolean(b) => write!(f, "{}", b),
            LambdaExpression::And(left, right) => write!(f, "({} and {})", left, right),
            LambdaExpression::Or(left, right) => write!(f, "({} or {})", left, right),
            LambdaExpression::Not(expr) => write!(f, "(not {})", expr),
            LambdaExpression::IsZero(expr) => write!(f, "(is_zero {})", expr),
            LambdaExpression::Multiply(left, right) => write!(f, "({} * {})", left, right),
            LambdaExpression::IfElse(condition, then_expr, else_expr) =>
                write!(f, "(if {} then {} else {})", condition, then_expr, else_expr),
        }
    }
}

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
}

pub fn parse_lambda(input: &str) -> Result<LambdaExpression, ParseError> {
    println!("Parsing input: {}", input);
    let mut tokens = tokenize(input);
    println!("Tokenized: {:?}", tokens.clone().collect::<Vec<_>>());
    let result = parse_lambda_expression(&mut tokens);

    if tokens.peek().is_some() {
        println!("Unexpected tokens at end of input: {:?}", tokens.collect::<Vec<_>>());
        Err(ParseError { message: "Unexpected tokens at end of input".to_string() })
    } else {
        println!("Parsed result: {:?}", result);
        result
    }
}

// 将 tokenize 函数设为公开
pub fn tokenize(input: &str) -> Peekable<IntoIter<String>> {
    let mut tokens = Vec::new();
    let mut current_token = String::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        match ch {
            '(' | ')' | '.' | 'λ' | '\\' => {
                if !current_token.is_empty() {
                    tokens.push(current_token);
                    current_token = String::new();
                }
                tokens.push(ch.to_string());
            }
            ' ' | '\t' | '\n' => {
                if !current_token.is_empty() {
                    tokens.push(current_token);
                    current_token = String::new();
                }
            }
            '/' if chars.peek() == Some(&'/') => {
                chars.find(|&c| c == '\n');
            }
            _ => current_token.push(ch),
        }
    }

    if !current_token.is_empty() {
        tokens.push(current_token);
    }

    tokens.into_iter().peekable()
}

fn parse_lambda_expression(tokens: &mut Peekable<IntoIter<String>>) -> Result<LambdaExpression, ParseError> {
    println!("Entering parse_lambda_expression");
    let mut expr = parse_atomic_expression(tokens)?;
    println!("Initial atomic expression: {:?}", expr);

    while let Some(token) = tokens.peek() {
        if token == ")" {
            break;
        }
        if token == "*" {
            tokens.next(); // consume "*"
            let right = parse_atomic_expression(tokens)?;
            expr = LambdaExpression::Multiply(Rc::new(expr), Rc::new(right));
            println!("Parsed multiplication: {:?}", expr);
        } else {
            let arg = parse_atomic_expression(tokens)?;
            println!("Parsed argument: {:?}", arg);
            expr = LambdaExpression::Application {
                function: Rc::new(expr),
                argument: Rc::new(arg),
            };
        }
        println!("Updated expression: {:?}", expr);
    }

    println!("Exiting parse_lambda_expression with: {:?}", expr);
    Ok(expr)
}

fn parse_atomic_expression(tokens: &mut Peekable<IntoIter<String>>) -> Result<LambdaExpression, ParseError> {
    match tokens.next() {
        Some(token) => {
            println!("Parsing atomic expression, token: {}", token);
            match token.as_str() {
                "λ" | "\\" => parse_abstraction(tokens),
                "(" => {
                    let inner_expr = parse_lambda_expression(tokens)?;
                    expect_token(tokens, ")")?;
                    Ok(inner_expr)
                },
                "pair" => {
                    let first = parse_atomic_expression(tokens)?;
                    let second = parse_atomic_expression(tokens)?;
                    Ok(LambdaExpression::Pair(Rc::new(first), Rc::new(second)))
                },
                "true" => Ok(parse_lambda("λx. λy. x").unwrap()),
                "false" => Ok(parse_lambda("λx. λy. y").unwrap()),
                "ifelse" => Ok(parse_lambda("λp. λa. λb. p a b").unwrap()),
                "add" => Ok(parse_lambda("λm. λn. λf. λx. m f (n f x)").unwrap()),
                "Y" => Ok(parse_lambda("λf. (λx. f (x x)) (λx. f (x x))").unwrap()),
                "pred" => parse_unary_op(tokens, LambdaExpression::Pred),
                "succ" => parse_unary_op(tokens, LambdaExpression::Succ),
                "fst" => parse_unary_op(tokens, LambdaExpression::Fst),
                "snd" => parse_unary_op(tokens, LambdaExpression::Snd),
                "and" => parse_binary_op(tokens, |a, b| LambdaExpression::And(a, b)),
                "or" => parse_binary_op(tokens, |a, b| LambdaExpression::Or(a, b)),
                "not" => parse_unary_op(tokens, LambdaExpression::Not),
                "is_zero" => {
                    let expr = parse_atomic_expression(tokens)?;
                    Ok(LambdaExpression::IsZero(Rc::new(expr)))
                },
                "*" => parse_binary_op(tokens, |a, b| LambdaExpression::Multiply(a, b)),
                _ => {
                    if let Ok(num) = token.parse::<i64>() {
                        println!("Parsed number: {}", num);
                        Ok(LambdaExpression::Number(num))
                    } else {
                        println!("Parsed variable: {}", token);
                        Ok(LambdaExpression::Variable(token))
                    }
                },
            }
        },
        None => {
            println!("Unexpected end of input in parse_atomic_expression");
            Err(ParseError { message: "Unexpected end of input".to_string() })
        },
    }
}

fn parse_ifelse(tokens: &mut Peekable<IntoIter<String>>) -> Result<LambdaExpression, ParseError> {
    let condition = parse_lambda_expression(tokens)?;
    let then_expr = parse_lambda_expression(tokens)?;
    let else_expr = parse_lambda_expression(tokens)?;
    println!("Parsed ifelse: condition={:?}, then={:?}, else={:?}", condition, then_expr, else_expr);
    Ok(LambdaExpression::IfElse(Rc::new(condition), Rc::new(then_expr), Rc::new(else_expr)))
}

fn parse_unary_op<F>(tokens: &mut Peekable<IntoIter<String>>, constructor: F) -> Result<LambdaExpression, ParseError>
where
    F: Fn(Rc<LambdaExpression>) -> LambdaExpression,
{
    let expr = parse_atomic_expression(tokens)?;
    Ok(constructor(Rc::new(expr)))
}

fn parse_binary_op<F>(tokens: &mut Peekable<IntoIter<String>>, constructor: F) -> Result<LambdaExpression, ParseError>
where
    F: Fn(Rc<LambdaExpression>, Rc<LambdaExpression>) -> LambdaExpression,
{
    let left = parse_atomic_expression(tokens)?;
    let right = parse_atomic_expression(tokens)?;
    Ok(constructor(Rc::new(left), Rc::new(right)))
}

fn parse_abstraction(tokens: &mut Peekable<IntoIter<String>>) -> Result<LambdaExpression, ParseError> {
    let mut parameters = Vec::new();
    while let Some(token) = tokens.next() {
        if token == "." {
            break;
        }
        parameters.push(token);
    }
    if parameters.is_empty() {
        return Err(ParseError { message: "Expected parameter after λ".to_string() });
    }
    let body = parse_lambda_expression(tokens)?;

    let mut expr = body;
    for param in parameters.into_iter().rev() {
        expr = LambdaExpression::Abstraction {
            parameter: param,
            body: Rc::new(expr),
        };
    }
    Ok(expr)
}

fn expect_token(tokens: &mut Peekable<IntoIter<String>>, expected: &str) -> Result<(), ParseError> {
    match tokens.next() {
        Some(token) if token == expected => Ok(()),
        Some(token) => Err(ParseError { message: format!("Expected '{}', found '{}'", expected, token) }),
        None => Err(ParseError { message: format!("Expected '{}', found end of input", expected) }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_application() {
        let input = "(λx. x) y";
        println!("Input: {}", input);
        let tokens = tokenize(input);
        println!("Tokens: {:?}", tokens);
        let result = parse_lambda(input);
        println!("Parsed result: {:?}", result);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        println!("Parsed expression: {:?}", expr);
        match expr {
            LambdaExpression::Application { function, argument } => {
                println!("Function: {:?}", function);
                println!("Argument: {:?}", argument);
                match &*function {
                    LambdaExpression::Abstraction { parameter, body } => {
                        assert_eq!(parameter, "x");
                        assert!(matches!(&**body, LambdaExpression::Variable(name) if name == "x"));
                    },
                    _ => panic!("Expected Abstraction, got {:?}", function),
                }
                assert!(matches!(&*argument, LambdaExpression::Variable(name) if name == "y"));
            },
            _ => panic!("Expected Application, got {:?}", expr),
        }
    }

    #[test]
    fn test_inline_comments() {
        let input = r#"
        (λx. x)  // This is a comment
        y"#;
        let result = parse_lambda(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        println!("Parsed expression: {:?}", expr);
        match expr {
            LambdaExpression::Application { function, argument } => {
                assert!(
                    matches!(
                        &*function,
                        LambdaExpression::Abstraction { parameter, body }
                        if parameter == "x" && matches!(&**body, LambdaExpression::Variable(name) if name == "x")
                    )
                );
                assert!(matches!(&*argument, LambdaExpression::Variable(name) if name == "y"));
            }
            _ => panic!("Expected Application, got {:?}", expr),
        }
    }

    #[test]
    fn test_nested_application() {
        let input = "(λf. λx. f (f x)) (λy. y) z";
        println!("Input: {}", input);
        let tokens = tokenize(input);
        println!("Tokens: {:?}", tokens.collect::<Vec<_>>());
        let result = parse_lambda(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        println!("Parsed expression: {:?}", expr);

        // 验证整体结构是一个应用
        match expr {
            LambdaExpression::Application { function, argument } => {
                // 验证函数部分是另一个应用
                match &*function {
                    LambdaExpression::Application { function: inner_function, argument: inner_argument } => {
                        // 验证内部函数是一个抽象
                        match &**inner_function {
                            LambdaExpression::Abstraction { parameter: f, body } => {
                                assert_eq!(f, "f");
                                // 验证 body 是另一个抽象
                                match &**body {
                                    LambdaExpression::Abstraction { parameter: x, body: inner_body } => {
                                        assert_eq!(x, "x");
                                        // 验证 inner_body 是一个应用
                                        match &**inner_body {
                                            LambdaExpression::Application { function: f1, argument: f_x } => {
                                                assert!(matches!(&**f1, LambdaExpression::Variable(name) if name == "f"));
                                                match &**f_x {
                                                    LambdaExpression::Application { function: f2, argument: x } => {
                                                        assert!(matches!(&**f2, LambdaExpression::Variable(name) if name == "f"));
                                                        assert!(matches!(&**x, LambdaExpression::Variable(name) if name == "x"));
                                                    }
                                                    _ => panic!("Expected f x, got {:?}", f_x),
                                                }
                                            }
                                            _ => panic!("Expected f (f x), got {:?}", inner_body),
                                        }
                                    }
                                    _ => panic!("Expected λx. ..., got {:?}", body),
                                }
                            }
                            _ => panic!("Expected λf. ..., got {:?}", inner_function),
                        }
                        // 验证内部参数是 λy. y
                        match &**inner_argument {
                            LambdaExpression::Abstraction { parameter, body } => {
                                assert_eq!(parameter, "y");
                                assert!(matches!(&**body, LambdaExpression::Variable(name) if name == "y"));
                            }
                            _ => panic!("Expected λy. y, got {:?}", inner_argument),
                        }
                    }
                    _ => panic!("Expected application, got {:?}", function),
                }
                // 验证外部参数是 z
                assert!(matches!(&*argument, LambdaExpression::Variable(name) if name == "z"));
            }
            _ => panic!("Expected application, got {:?}", expr),
        }
    }

    #[test]
    fn test_identity_function() {
        let input = "λx. x";
        let result = parse_lambda(input);
        assert!(result.is_ok());
        let expr = result.unwrap();
        match expr {
            LambdaExpression::Abstraction { parameter, body } => {
                assert_eq!(parameter, "x");
                assert!(matches!(&*body, LambdaExpression::Variable(name) if name == "x"));
            },
            _ => panic!("Expected Abstraction, got {:?}", expr),
        }
    }

    #[test]
    fn test_fibonacci() {
        let input = r#"
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
) 5
"#;

        let result = parse_lambda(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        println!("Parsed expression: {:?}", expr);

        // 验证整体结构: (λfib. λn. ...) 5
        match expr {
            LambdaExpression::Application { function, argument } => {
                // 验证函数部分: (λfib. λn. ...)
                match &*function {
                    LambdaExpression::Abstraction { parameter: fib_param, body: fib_body } => {
                        assert_eq!(fib_param, "fib");
                        match &**fib_body {
                            LambdaExpression::Abstraction { parameter: n_param, body: n_body } => {
                                assert_eq!(n_param, "n");
                                // 验证函数体: ((λf. λx. f (f x)) ...)
                                match &**n_body {
                                    LambdaExpression::Application { function: app1, argument: n_arg } => {
                                        match &**app1 {
                                            LambdaExpression::Application { function: app2, argument: arg2 } => {
                                                match &**app2 {
                                                    // 验证 Y 组合子: λf. λx. f (f x)
                                                    LambdaExpression::Application { function: y_combinator, argument: y_arg1 } => {
                                                        match &**y_combinator {
                                                            LambdaExpression::Abstraction { parameter: f_param, body: f_body } => {
                                                                assert_eq!(f_param, "f");
                                                                match &**f_body {
                                                                    LambdaExpression::Abstraction { parameter: x_param, body: x_body } => {
                                                                        assert_eq!(x_param, "x");
                                                                        // 验证 f (f x) 结构
                                                                        match &**x_body {
                                                                            LambdaExpression::Application { function: f1, argument: f_x } => {
                                                                                assert!(matches!(&**f1, LambdaExpression::Variable(name) if name == "f"));
                                                                                match &**f_x {
                                                                                    LambdaExpression::Application { function: f2, argument: x } => {
                                                                                        assert!(matches!(&**f2, LambdaExpression::Variable(name) if name == "f"));
                                                                                        assert!(matches!(&**x, LambdaExpression::Variable(name) if name == "x"));
                                                                                    }
                                                                                    _ => panic!("Expected f x, got {:?}", f_x),
                                                                                }
                                                                            }
                                                                            _ => panic!("Expected f (f x), got {:?}", x_body),
                                                                        }
                                                                    }
                                                                    _ => panic!("Expected λx. ..., got {:?}", f_body),
                                                                }
                                                            }
                                                            _ => panic!("Expected Y combinator structure, got {:?}", y_combinator),
                                                        }

                                                        // 证 Y 组合子的第一个参数: λf. λg. λn. ...
                                                        match &**y_arg1 {
                                                            LambdaExpression::Abstraction { parameter: f_param, body: f_body } => {
                                                                assert_eq!(f_param, "f");
                                                                match &**f_body {
                                                                    LambdaExpression::Abstraction { parameter: g_param, body: g_body } => {
                                                                        assert_eq!(g_param, "g");
                                                                        match &**g_body {
                                                                            LambdaExpression::Abstraction { parameter: n_param, body: _n_body } => {
                                                                                assert_eq!(n_param, "n");
                                                                                // 这里可以继续验证斐波那契函数的主体结构
                                                                                // 包括 lte、递归调用等
                                                                            }
                                                                            _ => panic!("Expected λn. ..., got {:?}", g_body),
                                                                        }
                                                                    }
                                                                    _ => panic!("Expected λg. ..., got {:?}", f_body),
                                                                }
                                                            }
                                                            _ => panic!("Expected λf. ..., got {:?}", y_arg1),
                                                        }
                                                    }
                                                    _ => panic!("Expected Y combinator application, got {:?}", app2),
                                                }

                                                // 验证 Y 组子的第二个参数（结构与第一个参数相同）
                                                match &**arg2 {
                                                    LambdaExpression::Abstraction { parameter: f_param, body: f_body } => {
                                                        assert_eq!(f_param, "f");
                                                        match &**f_body {
                                                            LambdaExpression::Abstraction { parameter: g_param, body: g_body } => {
                                                                assert_eq!(g_param, "g");
                                                                match &**g_body {
                                                                    LambdaExpression::Abstraction { parameter: n_param, body: _ } => {
                                                                        assert_eq!(n_param, "n");
                                                                        // 这里可以继续验证结构，如果需要的话
                                                                    }
                                                                    _ => panic!("Expected λn. ..., got {:?}", g_body),
                                                                }
                                                            }
                                                            _ => panic!("Expected λg. ..., got {:?}", f_body),
                                                        }
                                                    }
                                                    _ => panic!("Expected λf. ..., got {:?}", arg2),
                                                }
                                            }
                                            _ => panic!("Expected application, got {:?}", app1),
                                        }
                                        // 验证最后的参数 n
                                        assert!(matches!(&**n_arg, LambdaExpression::Variable(name) if name == "n"));
                                    }
                                    _ => panic!("Expected application, got {:?}", n_body),
                                }
                            }
                            _ => panic!("Expected λn. ..., got {:?}", fib_body),
                        }
                    }
                    _ => panic!("Expected λfib. ..., got {:?}", function),
                }

                // 验证参数是数字 5
                match &*argument {
                    LambdaExpression::Number(num) => {
                        assert_eq!(*num, 5);
                    }
                    _ => panic!("Expected Number 5, got {:?}", argument),
                }
            }
            _ => panic!("Expected Application, got {:?}", expr),
        }
    }

    #[test]
    fn test_pair() {
        let input = "pair 1 2";
        let result = parse_lambda(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        match expr {
            LambdaExpression::Pair(first, second) => {
                assert!(matches!(&*first, LambdaExpression::Number(1)));
                assert!(matches!(&*second, LambdaExpression::Number(2)));
            },
            _ => panic!("Expected Pair, got {:?}", expr),
        }
    }

    #[test]
    fn test_complex_pair() {
        let input = "pair (λx. x) (pair 1 2)";
        let result = parse_lambda(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        match expr {
            LambdaExpression::Pair(first, second) => {
                assert!(matches!(&*first, LambdaExpression::Abstraction { .. }));
                match &*second {
                    LambdaExpression::Pair(inner_first, inner_second) => {
                        assert!(matches!(&**inner_first, LambdaExpression::Number(1)));
                        assert!(matches!(&**inner_second, LambdaExpression::Number(2)));
                    },
                    _ => panic!("Expected inner Pair, got {:?}", second),
                }
            },
            _ => panic!("Expected Pair, got {:?}", expr),
        }
    }
}