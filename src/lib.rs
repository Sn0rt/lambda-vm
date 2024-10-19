pub mod lambda_parse;
pub mod lambda_vm;
pub mod repl;

pub use lambda_parse::LambdaExpression;
pub use lambda_vm::{VM, church_encode, church_decode};
pub use repl::run_repl;
