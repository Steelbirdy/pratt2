use logos::Logos;
use new_pratt::*;
use std::io::{BufRead, Write};
use std::iter::Peekable;

#[derive(Logos, Debug, PartialEq)]
enum Token {
    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,

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

    #[regex(r"\d+", |lex| lex.slice().parse())]
    Number(i32),

    #[error]
    #[regex(r"[ \t\r\n]+", logos::skip)]
    Error,
}

#[derive(Debug, PartialEq)]
enum Expr {
    Binary(Box<Expr>, Token, Box<Expr>),
    Prefix(Token, Box<Expr>),
    Number(i32),
}

#[derive(Debug)]
enum ParseError {
    PrattError(PrattError<Token>),
    EmptyParens,
    NoMatchingParen,
}

impl From<PrattError<Token>> for ParseError {
    fn from(err: PrattError<Token>) -> Self {
        Self::PrattError(err)
    }
}

struct Parser;

impl<I> PrattParser<I> for Parser
where
    I: Iterator<Item = Token>,
{
    type Input = Token;
    type Output = Expr;
    type Error = ParseError;

    fn query_affix(
        &mut self,
        token: &Self::Input,
        mode: ParseMode,
    ) -> Result<Option<Affix>, Self::Error> {
        let ret = match token {
            Token::LeftParen => Some(Affix::Nilfix),
            Token::RightParen => None,
            Token::Minus if mode.prefix() => Some(Affix::Prefix(Precedence(4))),
            Token::Plus | Token::Minus => Some(Affix::Infix(Precedence(1), Associativity::Left)),
            Token::Star | Token::Slash => Some(Affix::Infix(Precedence(2), Associativity::Left)),
            Token::Caret => Some(Affix::Infix(Precedence(3), Associativity::Right)),
            Token::Number(_) => Some(Affix::Nilfix),
            _ => panic!("unexpected token: {:?}", token),
        };
        Ok(ret)
    }

    fn nilfix(
        &mut self,
        token: Self::Input,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        let ret = match token {
            Token::LeftParen => {
                let inner = self
                    .parse_precedence(input, Precedence::MIN)
                    .and_then(|opt| opt.ok_or(ParseError::EmptyParens))?;
                input
                    .next_if_eq(&Token::RightParen)
                    .ok_or(ParseError::NoMatchingParen)?;
                inner
            }
            Token::Number(x) => Expr::Number(x),
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
        let ret = match op {
            Token::Minus => Expr::Prefix(op, Box::new(rhs)),
            _ => unreachable!(),
        };
        Ok(ret)
    }

    fn postfix(
        &mut self,
        _lhs: Self::Output,
        _op: Self::Input,
        _input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        unreachable!()
    }

    fn infix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        rhs: Self::Output,
        _: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        let ret = match op {
            Token::Plus | Token::Minus | Token::Star | Token::Slash | Token::Caret => {
                Expr::Binary(Box::new(lhs), op, Box::new(rhs))
            }
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
        match Parser.parse(&mut Token::lexer(line.trim())) {
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
        Parser.parse(&mut Token::lexer(input)).unwrap()
    }

    fn parse_err(input: &str) -> ParseError {
        Parser.parse(&mut Token::lexer(input)).unwrap_err()
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
    fn parse_prefix() {
        check(
            "-500",
            Expr::Prefix(Token::Minus, Box::new(Expr::Number(500))),
        );
        check(
            "---1",
            Expr::Prefix(
                Token::Minus,
                Box::new(Expr::Prefix(
                    Token::Minus,
                    Box::new(Expr::Prefix(Token::Minus, Box::new(Expr::Number(1)))),
                )),
            ),
        );
    }

    #[test]
    fn parse_binary() {
        check(
            "1 + 2",
            Expr::Binary(
                Box::new(Expr::Number(1)),
                Token::Plus,
                Box::new(Expr::Number(2)),
            ),
        );
        check(
            "10 -- 4",
            Expr::Binary(
                Box::new(Expr::Number(10)),
                Token::Minus,
                Box::new(Expr::Prefix(Token::Minus, Box::new(Expr::Number(4)))),
            ),
        );
        check(
            "1 * 2 + 3 / -4",
            Expr::Binary(
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(1)),
                    Token::Star,
                    Box::new(Expr::Number(2)),
                )),
                Token::Plus,
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(3)),
                    Token::Slash,
                    Box::new(Expr::Prefix(Token::Minus, Box::new(Expr::Number(4)))),
                )),
            ),
        );
        check(
            "2 ^ 3 ^ 4",
            Expr::Binary(
                Box::new(Expr::Number(2)),
                Token::Caret,
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(3)),
                    Token::Caret,
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
                Token::Star,
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(1)),
                    Token::Plus,
                    Box::new(Expr::Number(3)),
                )),
            ),
        );
        check(
            "2 * (1 + 2 * (1 + 2))",
            Expr::Binary(
                Box::new(Expr::Number(2)),
                Token::Star,
                Box::new(Expr::Binary(
                    Box::new(Expr::Number(1)),
                    Token::Plus,
                    Box::new(Expr::Binary(
                        Box::new(Expr::Number(2)),
                        Token::Star,
                        Box::new(Expr::Binary(
                            Box::new(Expr::Number(1)),
                            Token::Plus,
                            Box::new(Expr::Number(2)),
                        )),
                    )),
                )),
            ),
        )
    }

    #[test]
    fn errors() {
        check_err("", "PrattError(EmptyInput)");
        check_err("1 1", "PrattError(UnexpectedNilfix(Number(1)))");
        check_err("1 ** 1", "PrattError(UnexpectedInfix(Star))");
        check_err("1 + ()", "EmptyParens");
        check_err("1 * (2 + 3", "NoMatchingParen");
    }
}
