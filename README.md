# Lambda Calculus Interpreter

This project implements a Lambda Calculus interpreter in Rust. It supports various operations and Church encodings for numbers and boolean values.

## Supported Instructions

The interpreter supports the following instructions and operations:

1. **Basic Lambda Calculus**
   - Variable: `x`, `y`, `z`, etc.
   - Abstraction: `λx. <expression>`
   - Application: `(<expression> <expression>)`

2. **Church Numerals**
   - Encoding: Automatically handled by the interpreter
   - Decoding: Automatically handled by the interpreter
   - Predecessor: `pred`
   - Successor: `succ`
   - Is Zero: `is_zero`
   - Multiplication: `multiply` or `*`

3. **Church Booleans**
   - True: `true` (encoded as `λx. λy. x`)
   - False: `false` (encoded as `λx. λy. y`)
   - And: `and`
   - Or: `or`
   - Not: `not`

4. **Control Flow**
   - If-Then-Else: `ifthenelse`

5. **Pairs**
   - Create Pair: `pair`
   - First Element: `first`
   - Second Element: `second`

6. **Recursion**
   - Y Combinator: `Y`

## Usage Examples

Here are some examples of how to use the interpreter:

1. Church Numeral Operations:
   ```
   (multiply 2 3)
   (is_zero 0)
   (pred (succ 5))
   ```

2. Boolean Operations:
   ```
   (and true false)
   (or true false)
   (not true)
   ```

3. Conditional Statement:
   ```
   (ifthenelse (is_zero 0) 1 2)
   ```

4. Pair Operations:
   ```
   (pair 1 2)
   (first (pair 1 2))
   (second (pair 1 2))
   ```

5. Factorial using Y Combinator:
   ```
   (Y (λf. λn. (ifthenelse (is_zero n) 1 (multiply n (f (pred n))))))
   ```

## Running Tests

To run the tests and see examples of the interpreter in action, use the following command:
