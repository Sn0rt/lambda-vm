# Lambda Calculus Interpreter

This project implements a Lambda Calculus interpreter in Rust. It supports various operations and Church encodings for numbers and boolean values.

## REPL (Read-Eval-Print Loop)

This project includes a REPL for interactive use of the Lambda Calculus interpreter. To start the REPL, run the project's main executable.

### REPL Commands

The REPL supports the following commands:

- `:help` or `:?` - Show the help message
- `:exit` - Exit the REPL
- `:clear` - Clear the screen
- `:last` - Show the last result
- `:log <level>` - Set the log level (error, warn, info, debug, trace)

To evaluate a Lambda Calculus expression, simply type it into the REPL and press Enter.

### REPL Example

[![asciicast](https://asciinema.org/a/Vak2OEvfS9cNdmgSxuEmXYmkg.svg)](https://asciinema.org/a/Vak2OEvfS9cNdmgSxuEmXYmkg)

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

