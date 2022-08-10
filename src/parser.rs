use std::iter::Peekable;

use crate::expr::{Expr, Type};
use crate::lexer::{self, Token};

#[derive(Debug)]
pub enum Error {
    NoMoreTokens,
    ExpectedToken(Token, Token),
    ExpectedIdent(Token),
    UnexpectedToken(Token),
    TokensLeft(Vec<Token>),
}

type Result<T> = std::result::Result<T, Error>;

fn expect_token<T: Iterator<Item = Token>>(
    expected: Token,
    tokens: &mut Peekable<T>,
) -> Result<()> {
    let token = tokens.next().ok_or(Error::NoMoreTokens)?;
    if token != expected {
        return Err(Error::ExpectedToken(expected, token));
    }
    Ok(())
}

fn parse_ident<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<String> {
    let token = tokens.next().ok_or(Error::NoMoreTokens)?;
    match token {
        Token::Ident(var) => Ok(var),
        _ => Err(Error::ExpectedIdent(token)),
    }
}

fn parse_let_expr<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Expr> {
    expect_token(Token::Let, tokens)?;
    let var = parse_ident(tokens)?;
    expect_token(Token::Equal, tokens)?;
    let value = parse_expr_inner(tokens)?;
    expect_token(Token::In, tokens)?;
    let body = parse_expr_inner(tokens)?;
    Ok(Expr::Let(var, Box::new(value), Box::new(body)))
}

fn parse_idents<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Vec<String>> {
    let mut idents = Vec::new();
    while let Some(Token::Ident(_)) = tokens.peek() {
        let ident = parse_ident(tokens)?;
        idents.push(ident);
    }
    Ok(idents)
}

fn parse_fun_expr<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Expr> {
    expect_token(Token::Fun, tokens)?;
    let params = parse_idents(tokens)?;
    expect_token(Token::Arrow, tokens)?;
    let body = parse_expr_inner(tokens)?;
    Ok(Expr::Fun(params, Box::new(body)))
}

fn parse_paren_expr<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Expr> {
    expect_token(Token::LParen, tokens)?;
    let expr = parse_expr_inner(tokens)?;
    expect_token(Token::RParen, tokens)?;
    Ok(expr)
}

fn parse_var_expr<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Expr> {
    let var = parse_ident(tokens)?;
    Ok(Expr::Var(var))
}

fn parse_list<O, T: Iterator<Item = Token>>(
    tokens: &mut Peekable<T>,
    left: Token,
    right: Token,
    producer: &dyn Fn(&mut Peekable<T>) -> Result<O>,
) -> Result<Vec<O>> {
    expect_token(left, tokens)?;
    let mut xs: Vec<O> = Vec::new();
    loop {
        let x = producer(tokens)?;
        xs.push(x);
        match tokens.next() {
            Some(Token::Comma) => (),
            Some(token) if token == right => {
                break;
            }
            Some(token) => {
                return Err(Error::UnexpectedToken(token));
            }
            None => {
                return Err(Error::NoMoreTokens);
            }
        }
    }
    Ok(xs)
}

fn parse_call_expr<T: Iterator<Item = Token>>(
    tokens: &mut Peekable<T>,
    fn_expr: Expr,
) -> Result<Expr> {
    let args = parse_list(tokens, Token::LParen, Token::RParen, &parse_expr_inner)?;
    Ok(Expr::Call(Box::new(fn_expr), args))
}

// fn get_number<T: Iterator<Item = char>>(c: char, iter: &mut Peekable<T>) -> u64 {
fn parse_expr_inner<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Expr> {
    let token = tokens.peek().ok_or(Error::NoMoreTokens)?;

    let mut expr = match token {
        Token::Let => parse_let_expr(tokens),
        Token::Fun => parse_fun_expr(tokens),
        Token::LParen => parse_paren_expr(tokens),
        Token::Ident(_) => parse_var_expr(tokens),
        _ => Err(Error::UnexpectedToken(token.clone())),
    }?;

    while let Some(Token::LParen) = tokens.peek() {
        expr = parse_call_expr(tokens, expr)?;
    }

    Ok(expr)
}

fn check_tokens_left<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<()> {
    let tokens_left: Vec<Token> = tokens.collect();
    if !tokens_left.is_empty() {
        return Err(Error::TokensLeft(tokens_left));
    }
    Ok(())
}

pub fn parse_expr(input: &str) -> Result<Expr> {
    let mut tokens = lexer::lex(input).into_iter().peekable();

    let expr = parse_expr_inner(&mut tokens)?;

    check_tokens_left(&mut tokens)?;
    Ok(expr)
}

fn parse_paren_ty<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Type> {
    let mut ty_args = parse_list(tokens, Token::LParen, Token::RParen, &parse_ty_inner)?;
    if ty_args.len() == 1 {
        match tokens.peek() {
            Some(Token::Arrow) => (),
            _ => {
                return Ok(ty_args.pop().unwrap());
            }
        }
    }
    expect_token(Token::Arrow, tokens)?;
    let ret_ty = parse_ty_inner(tokens)?;
    Ok(Type::Arrow(ty_args, Box::new(ret_ty)))
}

fn parse_const_ty<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Type> {
    let ident = parse_ident(tokens)?;
    Ok(Type::Const(ident))
}

fn parse_ty_inner<T: Iterator<Item = Token>>(tokens: &mut Peekable<T>) -> Result<Type> {
    let token = tokens.peek().ok_or(Error::NoMoreTokens)?;

    let mut ty = match token {
        Token::LParen => parse_paren_ty(tokens),
        Token::Ident(_) => parse_const_ty(tokens),
        _ => {
            return Err(Error::UnexpectedToken(token.clone()));
        }
    }?;

    if let Some(Token::LBracket) = tokens.peek() {
        let ty_args = parse_list(tokens, Token::LBracket, Token::RBracket, &parse_ty_inner)?;
        ty = Type::App(Box::new(ty), ty_args);
    }

    if let Some(Token::Arrow) = tokens.peek() {
        expect_token(Token::Arrow, tokens)?;
        let ret_ty = parse_ty_inner(tokens)?;
        return Ok(Type::Arrow(vec![ty], Box::new(ret_ty)));
    }

    Ok(ty)
}

pub fn parse_ty(input: &str) -> Result<(Vec<String>, Type)> {
    let mut tokens = lexer::lex(input).into_iter().peekable();

    let mut vars = Vec::new();
    if let Some(Token::ForAll) = tokens.peek() {
        expect_token(Token::ForAll, &mut tokens)?;
        expect_token(Token::LBracket, &mut tokens)?;
        vars = parse_idents(&mut tokens)?;
        expect_token(Token::RBracket, &mut tokens)?;
    }

    let ty = parse_ty_inner(&mut tokens)?;

    check_tokens_left(&mut tokens)?;
    Ok((vars, ty))
}

#[cfg(test)]
mod tests {
    use crate::expr::Expr;

    enum Expected {
        Pass(Expr),
        Fail,
    }

    fn pass(expr: Expr) -> Expected {
        Expected::Pass(expr)
    }

    fn fail() -> Expected {
        Expected::Fail
    }

    fn var(name: &str) -> Expr {
        Expr::Var(name.to_owned())
    }

    fn call(f: Expr, args: Vec<Expr>) -> Expr {
        Expr::Call(Box::new(f), args)
    }

    fn let_(var: &str, value: Expr, body: Expr) -> Expr {
        Expr::Let(var.to_owned(), Box::new(value), Box::new(body))
    }

    fn fun(params: Vec<&str>, body: Expr) -> Expr {
        let params = params.into_iter().map(|param| param.to_owned()).collect();
        Expr::Fun(params, Box::new(body))
    }

    #[test]
    fn parse() {
        let cases: Vec<(&str, Expected)> = vec![
            ("", fail()),
            ("a", pass(var("a"))),
            ("f(x, y)", pass(call(var("f"), vec![var("x"), var("y")]))),
            (
                "f(x)(y)",
                pass(call(call(var("f"), vec![var("x")]), vec![var("y")])),
            ),
            (
                "let f = fun x y -> g(x, y) in f(a, b)",
                pass(let_(
                    "f",
                    fun(vec!["x", "y"], call(var("g"), vec![var("x"), var("y")])),
                    call(var("f"), vec![var("a"), var("b")]),
                )),
            ),
            (
                "let x = a in
                let y = b in
                f(x, y)",
                pass(let_(
                    "x",
                    var("a"),
                    let_("y", var("b"), call(var("f"), vec![var("x"), var("y")])),
                )),
            ),
            ("f x", fail()),
            ("let a = one", fail()),
            ("a, b", fail()),
            ("a = b", fail()),
            ("()", fail()),
            ("fun x, y -> y", fail()),
            ("fun x -> x", pass(fun(vec!["x"], var("x")))),
        ];
        for (input, expected) in cases {
            match expected {
                Expected::Pass(expected) => match super::parse_expr(input) {
                    Ok(actual) => assert_eq!(expected, actual),
                    Err(e) => panic!("expected {:?}, got {:?}", expected, e),
                },
                Expected::Fail => {
                    if let Ok(actual) = super::parse_expr(input) {
                        panic!("expected failure, got {:?}", actual)
                    }
                }
            }
        }
    }
}
