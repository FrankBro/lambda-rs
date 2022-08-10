use std::io::{self, BufRead};

use crate::{core::make_env, parser::parse_expr};

mod core;
mod expr;
mod infer;
mod lexer;
mod parser;

fn main() {
    println!("Enter an expression to infer the type");

    let mut env = make_env();
    let stdin = io::stdin();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let input = line.trim_end();
        match parse_expr(input) {
            Ok(expr) => match env.infer(&expr) {
                Ok(ty) => {
                    let ty_str = env.ty_to_string(&ty).unwrap();
                    println!(":: {}", ty_str);
                }
                Err(e) => {
                    println!("Infer error: {:?}", e);
                }
            },
            Err(e) => {
                println!("Parse error: {:?}", e);
            }
        }
    }
}
