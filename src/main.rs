use lambda_vm::run_repl;
use log::LevelFilter;
use env_logger::Env;

fn main() {
    env_logger::Builder::from_env(Env::default().default_filter_or("debug"))
        .filter_module("lambda_vm", LevelFilter::Debug)
        .filter_module("rustyline", LevelFilter::Warn)  // 将 rustyline 的日志级别设置为 Warn
        .format_timestamp(None)
        .init();

    run_repl();
}
