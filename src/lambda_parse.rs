use std::rc::Rc;
use std::iter::Peekable;
use std::vec::IntoIter;

// <expression>  :== <abstraction> | <application> | <variable>
// <abstraction> :== λ <variable> . <expression>
// <application> :== ( <expression> <expression> )
// <variable>    :== v1 | v2 | ...

#[derive(Clone, Debug)]
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
    Number(u64), // 新增：表示自然数
}

#[derive(Debug)]
pub struct ParseError {
    message: String,
}

pub fn parse_lambda(input: &str) -> Result<LambdaExpression, ParseError> {
    let mut tokens = tokenize(input);
    let result = parse_lambda_expression(&mut tokens);
    
    // 确保所有的 token 都被消耗
    if tokens.peek().is_some() {
        Err(ParseError { message: "Unexpected tokens at end of input".to_string() })
    } else {
        result
    }
}

fn tokenize(input: &str) -> Peekable<IntoIter<String>> {
    let mut tokens = Vec::new();
    let mut current_token = String::new();

    for ch in input.chars() {
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
        let arg = parse_atomic_expression(tokens)?;
        expr = LambdaExpression::Application {
            function: Rc::new(expr),
            argument: Rc::new(arg),
        };
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
                _ => {
                    // 尝试将 token 解析为数字
                    if let Ok(num) = token.parse::<u64>() {
                        Ok(LambdaExpression::Number(num))
                    } else {
                        Ok(LambdaExpression::Variable(token))
                    }
                },
            }
        },
        None => Err(ParseError { message: "Unexpected end of input".to_string() }),
    }
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
    
    // 从最内层的抽象开始构建
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
    fn test_nested_application() {
        let input = "(λf. λx. f (f x)) (λy. y) z";
        let result = parse_lambda(input);
        assert!(result.is_ok());
        // 可以添加更详细的结构检查
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
    fn test_complex_expression() {
        let input = "(λf. λx. f (f x)) (λy. y)";
        let result = parse_lambda(input);
        assert!(result.is_ok());
        // 可以添加更详细的结构检查
    }
}