use logos::Logos;
use new_pratt::*;
use std::{
    io::{BufRead, Write},
    iter::Peekable,
};

#[derive(Logos, Debug, PartialEq)]
enum TokenKind {
    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token(",")]
    Comma,

    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("^")]
    Caret,

    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier,
    #[regex(r"\d+")]
    Number,

    #[error]
    #[regex(r"[ \t\r\n]+", logos::skip)]
    Error,
}

#[derive(Debug)]
struct Token<'a> {
    kind: TokenKind,
    slice: &'a str,
}

struct Lexer<'a>(logos::Lexer<'a, TokenKind>);

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|kind| Token {
            kind,
            slice: self.0.slice(),
        })
    }
}

#[derive(Debug, PartialEq)]
enum Expr<'a> {
    Binary(Box<Expr<'a>>, TokenKind, Box<Expr<'a>>),
    Prefix(TokenKind, Box<Expr<'a>>),
    Call(Box<Expr<'a>>, Vec<Expr<'a>>),
    Number(i32),
    Variable(&'a str),
}

#[derive(Debug)]
enum ParseError<'a> {
    PrattError(PrattError<Token<'a>>),
    EmptyParens,
    NoMatchingParen,
}

impl<'a> From<PrattError<Token<'a>>> for ParseError<'a> {
    fn from(err: PrattError<Token<'a>>) -> Self {
        Self::PrattError(err)
    }
}

struct Parser;

impl Parser {
    fn consume<'a, I>(
        &mut self,
        input: &mut Peekable<&mut I>,
        expected: &TokenKind,
    ) -> Option<Token<'a>>
    where
        I: Iterator<Item = Token<'a>>,
    {
        input.next_if(|tok| &tok.kind == expected)
    }

    fn parse_delimited<'a, I>(
        &mut self,
        input: &mut Peekable<&mut I>,
        delimiter: &TokenKind,
    ) -> Result<Vec<Expr<'a>>, ParseError<'a>>
    where
        I: Iterator<Item = Token<'a>>,
    {
        let mut ret = Vec::new();
        ret.extend(self.parse_precedence(input, Precedence::MIN)?);
        while self.consume(input, delimiter).is_some() {
            ret.extend(self.parse_precedence(input, Precedence::MIN)?);
        }
        Ok(ret)
    }
}

impl<'a, I> PrattParser<I> for Parser
where
    I: Iterator<Item = Token<'a>>,
{
    type Input = Token<'a>;
    type Output = Expr<'a>;
    type Error = ParseError<'a>;

    fn query_affix(
        &mut self,
        token: &Self::Input,
        mode: ParseMode,
    ) -> Result<Option<Affix>, Self::Error> {
        use TokenKind::*;
        let ret = match token.kind {
            LeftParen if mode.postfix() => Some(Affix::Postfix(Precedence(6))),
            LeftParen => Some(Affix::Nilfix),
            RightParen | Comma => None,
            Minus if mode.prefix() => Some(Affix::Prefix(Precedence(5))),
            Plus | Minus => Some(Affix::Infix(Precedence(2), Associativity::Left)),
            Star | Slash => Some(Affix::Infix(Precedence(3), Associativity::Left)),
            Caret => Some(Affix::Infix(Precedence(4), Associativity::Right)),
            Number => Some(Affix::Nilfix),
            Identifier => Some(Affix::Nilfix),
            _ => panic!("unexpected token: {:?}", token),
        };
        Ok(ret)
    }

    fn nilfix(
        &mut self,
        token: Self::Input,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        let ret = match token.kind {
            TokenKind::LeftParen => {
                let inner = self
                    .parse_precedence(input, Precedence::MIN)
                    .and_then(|opt| opt.ok_or(ParseError::EmptyParens))?;
                self.consume(input, &TokenKind::RightParen)
                    .ok_or(ParseError::NoMatchingParen)?;
                inner
            }
            TokenKind::Number => Expr::Number(token.slice.parse().unwrap()),
            TokenKind::Identifier => Expr::Variable(token.slice),
            _ => unreachable!(),
        };
        Ok(ret)
    }

    fn prefix(
        &mut self,
        op: Self::Input,
        rhs: Self::Output,
        _input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        let ret = match op.kind {
            kind @ TokenKind::Minus => Expr::Prefix(kind, Box::new(rhs)),
            _ => unreachable!(),
        };
        Ok(ret)
    }

    fn postfix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        let ret = match op.kind {
            TokenKind::LeftParen => {
                let args = self.parse_delimited(input, &TokenKind::Comma)?;
                self.consume(input, &TokenKind::RightParen)
                    .ok_or(ParseError::NoMatchingParen)?;
                Expr::Call(Box::new(lhs), args)
            }
            _ => unreachable!(),
        };
        Ok(ret)
    }

    fn infix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        rhs: Self::Output,
        _input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        let ret = match op.kind {
            kind
            @
            (TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::Caret) => Expr::Binary(Box::new(lhs), kind, Box::new(rhs)),
            _ => unreachable!(),
        };
        Ok(ret)
    }

    fn custom(
        &mut self,
        _lhs: Option<Self::Output>,
        _token: Self::Input,
        _rhs: Option<Self::Output>,
        _input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        unreachable!()
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut stdout = std::io::stdout();
    print!("> ");
    stdout.flush()?;

    for line in std::io::stdin().lock().lines() {
        let line = line?;
        match Parser.parse(&mut Lexer(TokenKind::lexer(&line))) {
            Ok(expr) => println!("{:?}", expr),
            Err(why) => eprintln!("Error while parsing: {:?}", why),
        };
        print!("> ");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> Expr {
        Parser.parse(&mut Lexer(TokenKind::lexer(input))).unwrap()
    }

    fn parse_err(input: &str) -> ParseError {
        Parser
            .parse(&mut Lexer(TokenKind::lexer(input)))
            .unwrap_err()
    }

    fn check(input: &str, expected: Expr) {
        assert_eq!(parse(input), expected);
    }

    fn check_err(input: &str, expected: &str) {
        assert_eq!(&format!("{:?}", parse_err(input)), expected);
    }

    #[test]
    fn parse_number() {
        check("123", Expr::Number(123));
        check("1234567890", Expr::Number(1234567890));
    }

    #[test]
    fn parse_variable() {
        check("x", Expr::Variable("x"));
        check("_____1", Expr::Variable("_____1"));
        check("_", Expr::Variable("_"));
        check("abc_def_0123", Expr::Variable("abc_def_0123"));
    }

    #[test]
    fn parse_prefix() {
        check(
            "-500",
            Expr::Prefix(TokenKind::Minus, Box::new(Expr::Number(500))),
        );
    }

    #[test]
    fn parse_binary() {
        check(
            "1 + 2",
            Expr::Binary(
                Box::new(Expr::Number(1)),
                TokenKind::Plus,
                Box::new(Expr::Number(2)),
            ),
        );
        check(
            "10 -- 4",
            Expr::Binary(
                Box::new(Expr::Number(10)),
                TokenKind::Minus,
                Box::new(Expr::Prefix(TokenKind::Minus, Box::new(Expr::Number(4)))),
            ),
        );
        check(
            "1 * 2 + 3 / -4",
            Expr::Binary(
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(1)),
                    TokenKind::Star,
                    Box::new(Expr::Number(2)),
                )),
                TokenKind::Plus,
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(3)),
                    TokenKind::Slash,
                    Box::new(Expr::Prefix(TokenKind::Minus, Box::new(Expr::Number(4)))),
                )),
            ),
        );
        check(
            "-2^3",
            Expr::Binary(
                Box::new(Expr::Prefix(TokenKind::Minus, Box::new(Expr::Number(2)))),
                TokenKind::Caret,
                Box::new(Expr::Number(3)),
            ),
        );
        check(
            "2^3^4",
            Expr::Binary(
                Box::new(Expr::Number(2)),
                TokenKind::Caret,
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(3)),
                    TokenKind::Caret,
                    Box::new(Expr::Number(4)),
                )),
            ),
        );
    }

    #[test]
    fn parse_grouping() {
        check(
            "2 * (1 + 3)",
            Expr::Binary(
                Box::new(Expr::Number(2)),
                TokenKind::Star,
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(1)),
                    TokenKind::Plus,
                    Box::new(Expr::Number(3)),
                )),
            ),
        );
    }

    #[test]
    fn parse_call() {
        check("exp(x)", Expr::Call(Box::new(Expr::Variable("exp")), vec![Expr::Variable("x")]));
        check(
            "sum(1,2,3,) * -atan2(y, 2+x)",
            Expr::Binary(
                Box::new(Expr::Call(
                    Box::new(Expr::Variable("sum")),
                    vec![Expr::Number(1), Expr::Number(2), Expr::Number(3)],
                )),
                TokenKind::Star,
                Box::new(Expr::Prefix(
                    TokenKind::Minus,
                    Box::new(Expr::Call(
                        Box::new(Expr::Variable("atan2")),
                        vec![
                            Expr::Variable("y"),
                            Expr::Binary(
                                Box::new(Expr::Number(2)),
                                TokenKind::Plus,
                                Box::new(Expr::Variable("x")),
                            ),
                        ],
                    )),
                )),
            ),
        );
        check("(f - g)(x)", Expr::Call(
            Box::new(Expr::Binary(
                Box::new(Expr::Variable("f")),
                TokenKind::Minus,
                Box::new(Expr::Variable("g")),
            )),
            vec![Expr::Variable("x")],
        ))
    }

    #[test]
    fn errors() {
        check_err("", "PrattError(EmptyInput)");
        check_err(
            "1 1",
            r#"PrattError(UnexpectedNilfix(Token { kind: Number, slice: "1" }))"#,
        );
        check_err(
            "1 ** 1",
            r#"PrattError(UnexpectedInfix(Token { kind: Star, slice: "*" }))"#,
        );
        check_err("1 + ()", "EmptyParens");
        check_err("1 * (2 + 3", "NoMatchingParen");
    }
}
