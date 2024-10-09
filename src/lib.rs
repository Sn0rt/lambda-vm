pub mod lambda_parse;
pub mod lambda_vm;

pub use lambda_parse::LambdaExpression;
pub use lambda_vm::{VM, church_encode, church_decode};
