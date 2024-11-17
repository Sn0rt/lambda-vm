use crate::lambda_parse::{parse_lambda, LambdaExpression};
use crate::lambda_vm::{VM, church_decode};
use rustyline::error::ReadlineError;
use rustyline::Editor;
use log::{debug, LevelFilter};
use colored::*;
use std::rc::Rc;

fn print_help() {
    println!("{}", "╔═══════════════════════════════════════════════════╗".cyan());
    println!("{}", "║             Available Commands                    ║".cyan().bold());
    println!("{}", "╠═══════════════════════════════════════════════════╣".cyan());
    println!("║  {:<20} - Show this help message    ║", ":help".yellow());
    println!("║  {:<20} - Show this help message    ║", ":?".yellow());
    println!("║  {:<20} - Exit the REPL             ║", ":exit".yellow());
    println!("║  {:<20} - Clear the screen          ║", ":clear".yellow());
    println!("║  {:<20} - Show the last result      ║", ":last".yellow());
    println!("║  {:<20} - Set log level             ║", ":log <level>".yellow());
    println!("║    (error, warn, info, debug, trace)  ║");
    println!("{}", "╠═══════════════════════════════════════════════════╣".cyan());
    println!("{}", "║ Enter a lambda calculus expression to evaluate it ║".cyan());
    println!("{}", "╚═══════════════════════════════════════════════════╝".cyan());
}

pub fn run_repl() {
    println!("{}", "╔═══════════════════════════════════════════════╗".green());
    println!("{}", "║   Welcome to the Lambda Calculus REPL! 🧮λ    ║".green().bold());
    println!("{}", "╚═══════════════════════════════════════════════╝".green());
    println!("{}", "Type ':help' or ':?' for available commands.".cyan().italic());
    println!("{}", "Default log level is DEBUG. Use ':log <level>' to change.".cyan().italic());

    let mut rl = Editor::<()>::new();
    let vm = VM::new();
    let mut last_result: Option<Rc<LambdaExpression>> = None;

    loop {
        let readline = rl.readline(&format!("{}", "λ> ".green().bold()));
        match readline {
            Ok(line) => {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    continue;
                }
                rl.add_history_entry(line.as_str());

                if trimmed.starts_with(':') {
                    match trimmed {
                        ":exit" => break,
                        ":help" | ":?" => print_help(),
                        ":clear" => print!("\x1B[2J\x1B[1;1H"),  // ANSI escape code to clear screen
                        ":last" => {
                            if let Some(ref result) = last_result {
                                println!("{}", "╔═══ Last Result ═══╗".cyan());
                                println!("  {}", result.to_string().green());
                                println!("{}", "╚═══════════════════╝".cyan());
                            } else {
                                println!("{}", "No previous result available.".yellow().italic());
                            }
                        },
                        cmd if cmd.starts_with(":log ") => {
                            let parts: Vec<&str> = cmd.split_whitespace().collect();
                            if parts.len() == 2 {
                                match parts[1] {
                                    "error" => set_log_level(LevelFilter::Error),
                                    "warn" => set_log_level(LevelFilter::Warn),
                                    "info" => set_log_level(LevelFilter::Info),
                                    "debug" => set_log_level(LevelFilter::Debug),
                                    "trace" => set_log_level(LevelFilter::Trace),
                                    _ => println!("{}", "Invalid log level. Use error, warn, info, debug, or trace.".red()),
                                }
                            } else {
                                println!("{}", "Invalid log command. Use ':log <level>'.".red());
                            }
                        },
                        _ => println!("{}", "Unknown command. Type ':help' for available commands.".red()),
                    }
                } else {
                    match parse_lambda(trimmed) {
                        Ok(expr) => {
                            debug!("Parsed expression: {}", expr.to_string().yellow());
                            let result = vm.eval(&expr);
                            println!("{} {}", "Evaluation Result: ".cyan(), result.to_string().green());
                            // Attempt to decode Church numerals
                            match church_decode(&result) {
                                Ok(num) => println!("{} {}", "Decoded as Church numeral:".cyan(), num.to_string().blue().bold()),
                                Err(_) => debug!("Not a valid Church numeral"),
                            }

                            last_result = Some(result);
                        }
                        Err(e) => println!("{} {}", "Parse error:".red().bold(), e.to_string().red()),
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("{}", "CTRL-C".yellow().bold());
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("{}", "CTRL-D".yellow().bold());
                break;
            }
            Err(err) => {
                println!("{} {}", "Error:".red().bold(), format!("{:?}", err).red());
                break;
            }
        }
    }

    println!("{}", "Thank you for using Lambda Calculus REPL! Goodbye! 👋".green().bold());
}

fn set_log_level(level: LevelFilter) {
    log::set_max_level(level);
    println!("{} {}", "Log level set to:".cyan().bold(), format!("{:?}", level).green());
}
