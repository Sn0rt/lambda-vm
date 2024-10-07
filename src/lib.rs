pub mod lambda_parse;
pub mod lambda_vm;

pub use lambda_parse::LambdaExpression;
pub use lambda_vm::{VM, church_encode, church_decode};

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    #[test]
    fn test_fibonacci_calculation() {
        // 定义斐波那契函数的 Lambda 表达式
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

        let fib = lambda_parse::parse_lambda(fib_code).unwrap();
        let vm = VM::new();

        // 计算斐波那契数列的前10个数
        for i in 0..10 {
            let input = LambdaExpression::Application {
                function: Rc::new(fib.clone()),
                argument: Rc::new(church_encode(i)),
            };
            let result = vm.eval(&input);
            let decoded = church_decode(&result).unwrap();
            
            // 计算预期的斐波那契数
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
            println!("Fibonacci({}) = {}", i, decoded);
        }
    }
}