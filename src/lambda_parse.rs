use std::rc::Rc;
use std::iter::Peekable;
use std::vec::IntoIter;
use std::fmt;
use log::debug;

// <expression>  :== <abstraction> | <application> | <variable>
// <abstraction> :== λ <variable> . <expression>
// <application> :== ( <expression> <expression> )
// <variable>    :== v1 | v2 | ...

#[derive(Clone)]
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
    Number(Rc<LambdaExpression>),
    Pred(Rc<LambdaExpression>),
    Succ(Rc<LambdaExpression>),
    Pair(Rc<LambdaExpression>, Rc<LambdaExpression>),
    First(Rc<LambdaExpression>),
    Second(Rc<LambdaExpression>),
    Boolean(Rc<LambdaExpression>),
    And(Rc<LambdaExpression>, Rc<LambdaExpression>),
    Or(Rc<LambdaExpression>, Rc<LambdaExpression>),
    Not(Rc<LambdaExpression>),
    IsZero(Rc<LambdaExpression>),
    Multiply(Rc<LambdaExpression>, Rc<LambdaExpression>),
    IfThenElse(Rc<LambdaExpression>, Rc<LambdaExpression>, Rc<LambdaExpression>),
    YCombinator(Rc<LambdaExpression>),
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
            LambdaExpression::Pair(first, second) => write!(f, "(pair {} {})", first, second),
            LambdaExpression::First(expr) => write!(f, "(first {})", expr),
            LambdaExpression::Second(expr) => write!(f, "(second {})", expr),
            LambdaExpression::Boolean(b) => write!(f, "{}", b),
            LambdaExpression::And(left, right) => write!(f, "({} and {})", left, right),
            LambdaExpression::Or(left, right) => write!(f, "({} or {})", left, right),
            LambdaExpression::Not(expr) => write!(f, "(not {})", expr),
            LambdaExpression::IsZero(expr) => write!(f, "(is_zero {})", expr),
            LambdaExpression::Multiply(left, right) => write!(f, "({} * {})", left, right),
            LambdaExpression::IfThenElse(condition, then_expr, else_expr) =>
                write!(f, "(ifthenelse {} {} {})", condition, then_expr, else_expr),
            LambdaExpression::YCombinator(expr) => write!(f, "(Y {})", expr),
        }
    }
}

impl LambdaExpression {
    pub fn to_church_bool(&self) -> Option<bool> {
        match self {
            LambdaExpression::Abstraction { parameter: x, body } => {
                match &**body {
                    LambdaExpression::Abstraction { parameter: y, body: inner_body } => {
                        match &**inner_body {
                            LambdaExpression::Variable(name) if name == x => Some(true),
                            LambdaExpression::Variable(name) if name == y => Some(false),
                            _ => None,
                        }
                    },
                    _ => None,
                }
            },
            _ => None,
        }
    }
}

impl PartialEq for LambdaExpression {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LambdaExpression::Variable(a), LambdaExpression::Variable(b)) => a == b,
            (LambdaExpression::Abstraction { parameter: p1, body: b1 },
             LambdaExpression::Abstraction { parameter: p2, body: b2 }) => {
                p1 == p2 && b1 == b2
            },
            (LambdaExpression::Application { function: f1, argument: a1 },
             LambdaExpression::Application { function: f2, argument: a2 }) => {
                f1 == f2 && a1 == a2
            },
            (LambdaExpression::Number(n1), LambdaExpression::Number(n2)) => n1 == n2,
            (LambdaExpression::Boolean(b1), LambdaExpression::Boolean(b2)) => b1 == b2,
            (LambdaExpression::Pred(e1), LambdaExpression::Pred(e2)) => e1 == e2,
            (LambdaExpression::Succ(e1), LambdaExpression::Succ(e2)) => e1 == e2,
            (LambdaExpression::Pair(f1, s1), LambdaExpression::Pair(f2, s2)) => f1 == f2 && s1 == s2,
            (LambdaExpression::First(e1), LambdaExpression::First(e2)) => e1 == e2,
            (LambdaExpression::Second(e1), LambdaExpression::Second(e2)) => e1 == e2,
            (LambdaExpression::And(l1, r1), LambdaExpression::And(l2, r2)) => l1 == l2 && r1 == r2,
            (LambdaExpression::Or(l1, r1), LambdaExpression::Or(l2, r2)) => l1 == l2 && r1 == r2,
            (LambdaExpression::Not(e1), LambdaExpression::Not(e2)) => e1 == e2,
            (LambdaExpression::IsZero(e1), LambdaExpression::IsZero(e2)) => e1 == e2,
            (LambdaExpression::Multiply(l1, r1), LambdaExpression::Multiply(l2, r2)) => l1 == l2 && r1 == r2,
            (LambdaExpression::IfThenElse(c1, t1, e1), LambdaExpression::IfThenElse(c2, t2, e2)) =>
                c1 == c2 && t1 == t2 && e1 == e2,
            (LambdaExpression::YCombinator(e1), LambdaExpression::YCombinator(e2)) => e1 == e2,
            _ => false,
        }
    }
}

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

pub fn parse_lambda(input: &str) -> Result<LambdaExpression, ParseError> {
    let mut tokens = tokenize(input);
    let result = parse_lambda_expression(&mut tokens);

    if tokens.peek().is_some() {
        Err(ParseError { message: "Unexpected tokens at end of input".to_string() })
    } else {
        result
    }
}

pub fn tokenize(input: &str) -> Peekable<IntoIter<String>> {
    let mut tokens = Vec::new();
    let mut current_token = String::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        match ch {
            '(' | ')' | '.' => {
                if !current_token.is_empty() {
                    tokens.push(current_token);
                    current_token = String::new();
                }
                tokens.push(ch.to_string());
            }
            'λ' | '\\' => {
                if !current_token.is_empty() {
                    tokens.push(current_token);
                    current_token = String::new();
                }
                tokens.push("λ".to_string()); // Always use 'λ' for lambda
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
    let mut expr = parse_atomic_expression(tokens)?;
    while let Some(token) = tokens.peek() {
        if token == ")" {
            break;
        }
        if token == "*" {
            tokens.next(); // consume "*"
            let right = parse_atomic_expression(tokens)?;
            expr = LambdaExpression::Multiply(Rc::new(expr), Rc::new(right));
        } else {
            let arg = parse_atomic_expression(tokens)?;
            expr = LambdaExpression::Application {
                function: Rc::new(expr),
                argument: Rc::new(arg),
            };
        }
        debug!("parse_expr: {:?}", expr);
    }
    Ok(expr)
}

fn parse_atomic_expression(tokens: &mut Peekable<IntoIter<String>>) -> Result<LambdaExpression, ParseError> {
    match tokens.next() {
        Some(token) => {
            match token.as_str() {
                "λ" | "\\" => parse_abstraction(tokens),
                "(" => {
                    let inner_expr = parse_lambda_expression(tokens)?;
                    expect_token(tokens, ")")?;
                    Ok(inner_expr)
                },
                // pair
                "pair" => {
                    let first = parse_atomic_expression(tokens)?;
                    let second = parse_atomic_expression(tokens)?;
                    Ok(LambdaExpression::Pair(Rc::new(first), Rc::new(second)))
                },
                "first" => parse_unary_op(tokens, LambdaExpression::First),
                "second" => parse_unary_op(tokens, LambdaExpression::Second),

                // boolean
                "true" => Ok(parse_lambda("λx. λy. x").unwrap()),
                "false" => Ok(parse_lambda("λx. λy. y").unwrap()),

                // arithmetic
                "add" => Ok(parse_lambda("λm. λn. λf. λx. m f (n f x)").unwrap()),
                "multiply" => Ok(parse_lambda("λm. λn. λf. m (n f)").unwrap()),

                // logic operations
                "and" => parse_binary_op(tokens, LambdaExpression::And),
                "or" => parse_binary_op(tokens, LambdaExpression::Or),
                "not" => parse_unary_op(tokens, LambdaExpression::Not),

                // Y
                "Y" => {
                    let f = parse_atomic_expression(tokens)?;
                    Ok(LambdaExpression::YCombinator(Rc::new(f)))
                }

                // pred and succ
                "pred" => parse_unary_op(tokens, LambdaExpression::Pred),
                "succ" => parse_unary_op(tokens, LambdaExpression::Succ),

                // conditional
                "is_zero" => {
                    let expr = parse_atomic_expression(tokens)?;
                    Ok(LambdaExpression::IsZero(Rc::new(expr)))
                },
                "*" => parse_binary_op(tokens, LambdaExpression::Multiply),

                // branch
               "ifthenelse" => parse_ifthenelse(tokens, LambdaExpression::IfThenElse),

                _ => {
                    if let Ok(num) = token.parse::<u64>() {
                        Ok(church_encode(num))
                    } else {
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

fn parse_ifthenelse<F>(tokens: &mut Peekable<IntoIter<String>>, constructor: F) -> Result<LambdaExpression, ParseError>
where
    F: Fn(Rc<LambdaExpression>, Rc<LambdaExpression>, Rc<LambdaExpression>) -> LambdaExpression,
{
    let condition = parse_atomic_expression(tokens)?;
    let then_expr = parse_atomic_expression(tokens)?;
    let else_expr = parse_atomic_expression(tokens)?;
    Ok(constructor(Rc::new(condition), Rc::new(then_expr), Rc::new(else_expr)))
}

fn parse_abstraction(tokens: &mut Peekable<IntoIter<String>>) -> Result<LambdaExpression, ParseError> {
    let mut parameters = Vec::new();
    for token in tokens.by_ref() {
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

fn church_encode(n: u64) -> LambdaExpression {
    let body = (0..n).fold(
        LambdaExpression::Variable("x".to_string()),
        |acc, _| LambdaExpression::Application {
            function: Rc::new(LambdaExpression::Variable("f".to_string())),
            argument: Rc::new(acc),
        },
    );
    LambdaExpression::Abstraction {
        parameter: "f".to_string(),
        body: Rc::new(LambdaExpression::Abstraction {
            parameter: "x".to_string(),
            body: Rc::new(body),
        }),
    }
}



impl From<i32> for LambdaExpression {
    fn from(n: i32) -> Self {
        church_encode(n as u64)
    }
}

impl From<bool> for LambdaExpression {
    fn from(b: bool) -> Self {
        if b {
            parse_lambda("λx. λy. x").unwrap()
        } else {
            parse_lambda("λx. λy. y").unwrap()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_church_numeral(expr: &LambdaExpression, value: usize) -> bool {
        match expr {
            LambdaExpression::Application { function, argument } => {
                if value == 0 {
                    false
                } else {
                    matches!(&**function, LambdaExpression::Variable(name) if name == "f") &&
                    is_church_numeral(argument, value - 1)
                }
            }
            LambdaExpression::Variable(name) => value == 0 && name == "x",
            _ => false,
        }
    }

    #[test]
    fn test_ifthenelse() {
        let input = "ifthenelse true 1 2";
        let result = parse_lambda(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        println!("Parsed expression: {:?}", expr);
        match expr {
            LambdaExpression::IfThenElse(condition, then_expr, else_expr) => {
                assert!(matches!(&*condition, LambdaExpression::Abstraction { .. }), "Condition should be a Church boolean");

                // Check if then_expr is a Church encoding of 1
                assert!(matches!(&*then_expr, LambdaExpression::Abstraction { parameter: f, body }
                    if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                        if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                            function,
                            argument
                        } if matches!(&**function, LambdaExpression::Variable(name) if name == "f")
                            && matches!(&**argument, LambdaExpression::Variable(name) if name == "x"))
                    )
                ), "Then expression should be Church encoding of 1");

                // Check if else_expr is a Church encoding of 2
                assert!(matches!(&*else_expr, LambdaExpression::Abstraction { parameter: f, body }
                    if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                        if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                            function: outer_f,
                            argument: outer_arg
                        } if matches!(&**outer_f, LambdaExpression::Variable(name) if name == "f")
                            && matches!(&**outer_arg, LambdaExpression::Application {
                                function: inner_f,
                                argument: inner_arg
                            } if matches!(&**inner_f, LambdaExpression::Variable(name) if name == "f")
                                && matches!(&**inner_arg, LambdaExpression::Variable(name) if name == "x"))
                        )
                    )
                ), "Else expression should be Church encoding of 2");
            }
            _ => panic!("Expected IfThenElse, got {:?}", expr),
        }
    }

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

        match expr {
            LambdaExpression::Application { function, argument } => {
                match &*function {
                    LambdaExpression::Application { function: inner_function, argument: inner_argument } => {
                        match &**inner_function {
                            LambdaExpression::Abstraction { parameter: f, body } => {
                                assert_eq!(f, "f");
                                match &**body {
                                    LambdaExpression::Abstraction { parameter: x, body: inner_body } => {
                                        assert_eq!(x, "x");
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

        match expr {
            LambdaExpression::Application { function, argument } => {
                match &*function {
                    LambdaExpression::Abstraction { parameter: fib_param, body: fib_body } => {
                        assert_eq!(fib_param, "fib");
                        match &**fib_body {
                            LambdaExpression::Abstraction { parameter: n_param, body: n_body } => {
                                assert_eq!(n_param, "n");
                                // The body structure is complex, so we'll just check if it's an Application
                                assert!(matches!(&**n_body, LambdaExpression::Application { .. }));
                            }
                            _ => panic!("Expected λn. ..., got {:?}", fib_body),
                        }
                    }
                    _ => panic!("Expected λfib. ..., got {:?}", function),
                }

                // Check if the argument is a Church encoding of 5
                assert!(matches!(&*argument, LambdaExpression::Abstraction { parameter: f, body }
                    if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                        if x == "x" && is_church_numeral(&inner_body, 5)
                    )
                ), "Argument should be Church encoding of 5");
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
                // Check if first is a Church encoding of 1
                assert!(matches!(&*first, LambdaExpression::Abstraction { parameter: f, body }
                    if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                        if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                            function,
                            argument
                        } if matches!(&**function, LambdaExpression::Variable(name) if name == "f")
                            && matches!(&**argument, LambdaExpression::Variable(name) if name == "x"))
                    )
                ), "First element should be Church encoding of 1");

                // Check if second is a Church encoding of 2
                assert!(matches!(&*second, LambdaExpression::Abstraction { parameter: f, body }
                    if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                        if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                            function: outer_f,
                            argument: outer_arg
                        } if matches!(&**outer_f, LambdaExpression::Variable(name) if name == "f")
                            && matches!(&**outer_arg, LambdaExpression::Application {
                                function: inner_f,
                                argument: inner_arg
                            } if matches!(&**inner_f, LambdaExpression::Variable(name) if name == "f")
                                && matches!(&**inner_arg, LambdaExpression::Variable(name) if name == "x"))
                        )
                    )
                ), "Second element should be Church encoding of 2");
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
                        // Check if inner_first is a Church encoding of 1
                        assert!(matches!(&**inner_first, LambdaExpression::Abstraction { parameter: f, body }
                            if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                                if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                                    function,
                                    argument
                                } if matches!(&**function, LambdaExpression::Variable(name) if name == "f")
                                    && matches!(&**argument, LambdaExpression::Variable(name) if name == "x"))
                            )
                        ), "First element of inner pair should be Church encoding of 1");

                        // Check if inner_second is a Church encoding of 2
                        assert!(matches!(&**inner_second, LambdaExpression::Abstraction { parameter: f, body }
                            if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                                if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                                    function: outer_f,
                                    argument: outer_arg
                                } if matches!(&**outer_f, LambdaExpression::Variable(name) if name == "f")
                                    && matches!(&**outer_arg, LambdaExpression::Application {
                                        function: inner_f,
                                        argument: inner_arg
                                    } if matches!(&**inner_f, LambdaExpression::Variable(name) if name == "f")
                                        && matches!(&**inner_arg, LambdaExpression::Variable(name) if name == "x"))
                                )
                            )
                        ), "Second element of inner pair should be Church encoding of 2");
                    },
                    _ => panic!("Expected inner Pair, got {:?}", second),
                }
            },
            _ => panic!("Expected Pair, got {:?}", expr),
        }
    }

    #[test]
    fn test_pair_operations() {
        let input = "second (pair (first (pair 1 2)) 3)";
        let result = parse_lambda(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        match expr {
            LambdaExpression::Second(pair) => {
                match &*pair {
                    LambdaExpression::Pair(first, second) => {
                        match &**first {
                            LambdaExpression::First(inner_pair) => {
                                match &**inner_pair {
                                    LambdaExpression::Pair(inner_first, inner_second) => {
                                        // Check if inner_first is a Church encoding of 1
                                        assert!(matches!(&**inner_first, LambdaExpression::Abstraction { parameter: f, body }
                                            if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                                                if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                                                    function,
                                                    argument
                                                } if matches!(&**function, LambdaExpression::Variable(name) if name == "f")
                                                    && matches!(&**argument, LambdaExpression::Variable(name) if name == "x"))
                                            )
                                        ), "First element of inner pair should be Church encoding of 1");

                                        // Check if inner_second is a Church encoding of 2
                                        assert!(matches!(&**inner_second, LambdaExpression::Abstraction { parameter: f, body }
                                            if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                                                if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                                                    function: outer_f,
                                                    argument: outer_arg
                                                } if matches!(&**outer_f, LambdaExpression::Variable(name) if name == "f")
                                                    && matches!(&**outer_arg, LambdaExpression::Application {
                                                        function: inner_f,
                                                        argument: inner_arg
                                                    } if matches!(&**inner_f, LambdaExpression::Variable(name) if name == "f")
                                                        && matches!(&**inner_arg, LambdaExpression::Variable(name) if name == "x"))
                                                )
                                            )
                                        ), "Second element of inner pair should be Church encoding of 2");
                                    },
                                    _ => panic!("Expected Pair, got {:?}", inner_pair),
                                }
                            },
                            _ => panic!("Expected First, got {:?}", first),
                        }
                        // Check if second is a Church encoding of 3
                        assert!(matches!(&**second, LambdaExpression::Abstraction { parameter: f, body }
                            if f == "f" && matches!(&**body, LambdaExpression::Abstraction { parameter: x, body: inner_body }
                                if x == "x" && matches!(&**inner_body, LambdaExpression::Application {
                                    function: f1,
                                    argument: arg1
                                } if matches!(&**f1, LambdaExpression::Variable(name) if name == "f")
                                    && matches!(&**arg1, LambdaExpression::Application {
                                        function: f2,
                                        argument: arg2
                                    } if matches!(&**f2, LambdaExpression::Variable(name) if name == "f")
                                        && matches!(&**arg2, LambdaExpression::Application {
                                            function: f3,
                                            argument: arg3
                                        } if matches!(&**f3, LambdaExpression::Variable(name) if name == "f")
                                            && matches!(&**arg3, LambdaExpression::Variable(name) if name == "x")))
                                )
                            )
                        ), "Second element should be Church encoding of 3");
                    },
                    _ => panic!("Expected Pair, got {:?}", pair),
                }
            },
            _ => panic!("Expected Second, got {:?}", expr),
        }
    }

    #[test]
    fn test_factorial3() {
        let input = r"
            Y (λf. λn.
                ifthenelse (is_zero n)
                    1
                    (multiply n (f (pred n))))
        ";
        let result = parse_lambda(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
        let expr = result.unwrap();
        println!("Parsed expression: {:?}", expr);

        // Define the expected structure
        let expected = LambdaExpression::YCombinator(Rc::new(
            LambdaExpression::Abstraction {
                parameter: "f".to_string(),
                body: Rc::new(LambdaExpression::Abstraction {
                    parameter: "n".to_string(),
                    body: Rc::new(LambdaExpression::IfThenElse(
                        Rc::new(LambdaExpression::IsZero(Rc::new(LambdaExpression::Variable("n".to_string())))),
                        Rc::new(church_encode(1)),
                        Rc::new(LambdaExpression::Application {
                            function: Rc::new(LambdaExpression::Application {
                                function: Rc::new(parse_lambda("λm. λn. λf. m (n f)").unwrap()),
                                argument: Rc::new(LambdaExpression::Variable("n".to_string())),
                            }),
                            argument: Rc::new(LambdaExpression::Application {
                                function: Rc::new(LambdaExpression::Variable("f".to_string())),
                                argument: Rc::new(LambdaExpression::Pred(Rc::new(LambdaExpression::Variable("n".to_string()))))
                            })
                        })
                    ))
                })
            }
        ));

        // Compare the parsed expression with the expected structure
        assert_eq!(expr, expected, "Parsed expression does not match the expected structure");
    }
}