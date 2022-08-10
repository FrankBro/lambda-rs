use logos::{Lexer, Logos};

fn ident(lex: &mut Lexer<Token>) -> Option<String> {
    let slice = lex.slice();
    let ident: String = slice[..slice.len()].parse().ok()?;
    Some(ident)
}

#[derive(Logos, Clone, Debug, PartialEq)]
pub enum Token {
    #[token("let")]
    Let,
    #[token("=")]
    Equal,
    #[token("in")]
    In,
    #[token("fun")]
    Fun,
    #[token("->")]
    Arrow,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(",")]
    Comma,
    #[token("forall")]
    ForAll,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*", ident)]
    Ident(String),

    #[error]
    #[regex(r"[ \t\n\r\f]+", logos::skip)]
    Error,
}

pub fn lex(input: &str) -> Vec<Token> {
    let lex = Token::lexer(input);
    let mut tokens = Vec::new();
    for token in lex {
        tokens.push(token);
    }
    tokens
}

#[cfg(test)]
mod tests {
    use logos::Logos;

    use super::Token;

    #[test]
    fn tests() {
        let cases = vec![
            ("", vec![]),
            ("  \t\n\n\t\r\n\r", vec![]),
            (
                "())in,let_ _1Ma->==",
                vec![
                    Token::LParen,
                    Token::RParen,
                    Token::RParen,
                    Token::In,
                    Token::Comma,
                    Token::Ident("let_".to_owned()),
                    Token::Ident("_1Ma".to_owned()),
                    Token::Arrow,
                    Token::Equal,
                    Token::Equal,
                ],
            ),
            ("let fun in", vec![Token::Let, Token::Fun, Token::In]),
            (";", vec![Token::Error]),
        ];
        for (input, expected) in cases {
            let lex = Token::lexer(input);
            let mut actual = Vec::new();
            for token in lex {
                actual.push(token);
            }
            assert_eq!(expected, actual);
        }
    }
}
