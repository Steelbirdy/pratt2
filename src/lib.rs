/// This crate provides a high-level interface for implementing Pratt parsers in Rust.
///
/// > In computer science, a Pratt parser is an improved recursive descent parser that
/// > associates semantics with tokens instead of grammar rules.
/// * https://en.wikipedia.org/wiki/Pratt_parser
///
/// In other words, you can use a Pratt parser to parse expressions that might contain *unary* and
/// *binary* operators of varying *precedence* and *associativity*.
///
/// The documentation provides some simple examples. See the `examples` folder in the
/// repository for more in-depth use cases.
///
/// # Example: simple arithmetic
///
/// We will use [logos](https://docs.rs/logos/0.12.0/logos/) to tokenize the input expression, then
/// use a Pratt parser to convert it into an expression tree.
///
/// ```rust
/// use logos::Logos;
/// use new_pratt::*;
/// use std::iter::Peekable;
///
/// #[derive(Debug, PartialEq)]
/// enum Expr {
///     Number(i32),
///     Binary(Box<Expr>, BinaryOperator, Box<Expr>),
///     Prefix(UnaryOperator, Box<Expr>),
///     Postfix(Box<Expr>, UnaryOperator)
/// }
///
/// #[derive(Debug, PartialEq)]
/// enum BinaryOperator {
///     Add,
///     Sub,
///     Mul,
///     Div,
///     Pow,
/// }
///
/// #[derive(Debug, PartialEq)]
/// enum UnaryOperator {
///     // Negation
///     Neg,
///     // Factorial
///     Fac,
/// }
///
/// #[derive(Logos, Debug, PartialEq)]
/// enum Token {
///     #[token("+")]
///     Plus,
///     #[token("-")]
///     Minus,
///     #[token("*")]
///     Star,
///     #[token("/")]
///     Slash,
///     #[token("^")]
///     Caret,
///     #[token("!")]
///     Bang,
///
///     #[regex(r"\d+", |lex| lex.slice().parse())]
///     Number(i32),
///
///     #[error]
///     #[regex(r"[ \t\r\n]+", logos::skip)]
///     Error,
/// }
///
/// fn tokenize(input: &str) -> impl Iterator<Item = Token> {
///     Token::lexer(input)
/// }
///
/// struct Parser;
///
/// impl<I> PrattParser<I> for Parser
/// where
///     I: Iterator<Item = Token>,
/// {
///     type Input = Token;
///     type Output = Expr;
///     type Error = PrattError<Self::Input>;
///
///     fn query_affix(&mut self, token: &Self::Input, mode: ParseMode) -> Result<Option<Affix>, Self::Error> {
///         let ret = match token {
///             // Differentiate between unary negation and binary subtraction. If the parser
///             // is prepared to accept prefix tokens, parse '-' as negation.
///             Token::Minus if mode.prefix() => Some(Affix::Prefix(Precedence(5))),
///             Token::Plus | Token::Minus => Some(Affix::Infix(Precedence(2), Associativity::Left)),
///             Token::Star | Token::Slash => Some(Affix::Infix(Precedence(3), Associativity::Left)),
///             Token::Caret => Some(Affix::Infix(Precedence(4), Associativity::Right)),
///             Token::Bang => Some(Affix::Postfix(Precedence(6))),
///             Token::Number(_) => Some(Affix::Nilfix),
///             _ => panic!("unexpected token: {:?}", token),
///         };
///         Ok(ret)
///     }
///
///     fn nilfix(&mut self, token: Self::Input, _: &mut Peekable<&mut I>) -> Result<Self::Output, Self::Error> {
///         match token {
///             Token::Number(x) => Ok(Expr::Number(x)),
///             _ => unreachable!(),
///         }
///     }
///
///     fn prefix(&mut self, op: Self::Input, rhs: Self::Output, _: &mut Peekable<&mut I>) -> Result<Self::Output, Self::Error> {
///         let op = match op {
///             Token::Minus => UnaryOperator::Neg,
///             _ => unreachable!(),
///         };
///         Ok(Expr::Prefix(op, Box::new(rhs)))
///     }
///
///     fn postfix(&mut self, lhs: Self::Output, op: Self::Input, _: &mut Peekable<&mut I>) -> Result<Self::Output, Self::Error> {
///         let op = match op {
///             Token::Bang => UnaryOperator::Fac,
///             _ => unreachable!(),
///         };
///         Ok(Expr::Postfix(Box::new(lhs), op))
///     }
///
///     fn infix(&mut self, lhs: Self::Output, op: Self::Input, rhs: Self::Output, _: &mut Peekable<&mut I>) -> Result<Self::Output, Self::Error> {
///         let op = match op {
///             Token::Plus => BinaryOperator::Add,
///             Token::Minus => BinaryOperator::Sub,
///             Token::Star => BinaryOperator::Mul,
///             Token::Slash => BinaryOperator::Div,
///             Token::Caret => BinaryOperator::Pow,
///             _ => unreachable!(),
///         };
///         Ok(Expr::Binary(Box::new(lhs), op, Box::new(rhs)))
///     }
///
///     fn custom(&mut self, lhs: Option<Self::Output>, token: Self::Input, rhs: Option<Self::Output>, input: &mut Peekable<&mut I>) -> Result<Self::Output, Self::Error> {
///         unreachable!()
///     }
/// }
///
/// fn parse(input: &str) -> Result<Expr, PrattError<Token>> {
///     Parser.parse(&mut tokenize(input))
/// }
/// ```

use std::fmt;
use std::iter::Peekable;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct Precedence(pub u32);

impl Precedence {
    pub const MIN: Precedence = Precedence(u32::MIN);

    pub const MAX: Precedence = Precedence(u32::MAX);

    pub const fn lower(mut self) -> Precedence {
        if let Some(x) = self.0.checked_sub(1) {
            self.0 = x;
        }
        self
    }

    pub const fn raise(mut self) -> Precedence {
        if let Some(x) = self.0.checked_add(1) {
            self.0 = x;
        }
        self
    }

    const fn normalize(mut self) -> Precedence {
        if let Some(x) = self.0.checked_mul(10) {
            self.0 = x;
        }
        self
    }
}

#[non_exhaustive]
#[derive(Debug)]
pub enum Associativity {
    Left,
    Right,
    Neither,
}

#[non_exhaustive]
#[derive(Debug)]
pub enum Affix {
    /// Used for a primary token with no arguments, such as a number or an identifier.
    Nilfix,
    /// Used for a prefix operator with a single right-hand argument,
    /// such as '!' (not) or '-' (negation).
    Prefix(Precedence),
    /// Used for a postfix operator with a single left-hand argument, such as '?' (try).
    Postfix(Precedence),
    /// Used for an infix operator with a left- and a right-hand argument,
    /// such as '+' (addition) or '*' (multiplication).
    Infix(Precedence, Associativity),
    /// Used for custom tokens with optional left- and right-hand arguments.
    Custom(Precedence, Precedence),
}

impl Affix {
    pub const fn left_precedence(&self) -> Precedence {
        match self {
            Self::Nilfix => Precedence::MAX,
            Self::Prefix(_) => Precedence::MAX,
            Self::Postfix(p) => p.normalize(),
            Self::Infix(p, _) => p.normalize(),
            Self::Custom(p, _) => p.normalize(),
        }
    }

    pub const fn right_precedence(&self) -> Precedence {
        match self {
            Self::Nilfix => Precedence::MAX,
            Self::Prefix(p) => p.normalize(),
            Self::Postfix(_) => Precedence::MAX,
            Self::Infix(p, Associativity::Left) => p.normalize().raise(),
            Self::Infix(p, Associativity::Right) => p.normalize().lower(),
            Self::Infix(p, Associativity::Neither) => p.normalize(),
            Self::Custom(_, p) => p.normalize(),
        }
    }
}

/// Represents the current state of the parser including what kinds of tokens it is prepared to
/// accept.
pub struct ParseMode(__ParseMode);

#[doc(hidden)]
pub enum __ParseMode {
    PrefixNilfix,
    PostfixInfix,
}

impl ParseMode {
    /// Returns true if and only if the parser could accept a nilfix token in its current state.
    pub fn nilfix(&self) -> bool {
        matches!(self.0, __ParseMode::PrefixNilfix)
    }

    /// Returns true if and only if the parser could accept a prefix operator in its current state.
    pub fn prefix(&self) -> bool {
        matches!(self.0, __ParseMode::PrefixNilfix)
    }

    /// Returns true if and only if the parser could accept a postfix operator in its current state.
    pub fn postfix(&self) -> bool {
        matches!(self.0, __ParseMode::PostfixInfix)
    }

    /// Returns true if and only if the parser could accept an infix operator in its current state.
    pub fn infix(&self) -> bool {
        matches!(self.0, __ParseMode::PostfixInfix)
    }
}

#[derive(Debug)]
pub enum PrattError<I: fmt::Debug> {
    EmptyInput,
    UnexpectedNilfix(I),
    UnexpectedPrefix(I),
    UnexpectedPostfix(I),
    UnexpectedInfix(I),
}

impl<I: fmt::Debug> fmt::Display for PrattError<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => write!(f, "parser was called with empty input"),
            Self::UnexpectedNilfix(token) => {
                write!(f, "expected infix or postfix, found nilfix: `{:?}`", token)
            }
            Self::UnexpectedPrefix(token) => {
                write!(f, "expected infix or postfix, found prefix: `{:?}`", token)
            }
            Self::UnexpectedPostfix(token) => {
                write!(f, "expected nilfix or prefix, found postfix: `{:?}`", token)
            }
            Self::UnexpectedInfix(token) => {
                write!(f, "expected nilfix or prefix, found infix: `{:?}`", token)
            }
        }
    }
}

pub trait PrattParser<I>
where
    I: Iterator<Item = Self::Input>,
{
    type Input: fmt::Debug;
    type Output;
    type Error: From<PrattError<Self::Input>>;

    /// Returns the affix of `token`.
    ///
    /// `None` indicates that the parser should stop parsing at the current depth without
    /// consuming `token`.
    ///
    /// `mode` gives context that allows a single token to be parsed differently depending on
    /// the current state of the parser.
    ///
    /// See the examples for more information.
    /// ```
    fn query_affix(&mut self, token: &Self::Input, mode: ParseMode) -> Result<Option<Affix>, Self::Error>;

    /// Converts a nilfix (primary) token into an output and returns it.
    fn nilfix(
        &mut self,
        token: Self::Input,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    /// Converts a prefix operator and its argument into an output and returns it.
    fn prefix(
        &mut self,
        op: Self::Input,
        rhs: Self::Output,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    /// Converts a postfix operator and its argument into an output and returns it.
    fn postfix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    /// Converts an infix operator and its arguments into an output and returns it.
    fn infix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        rhs: Self::Output,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    /// Converts a non-regular token and (optionally) its arguments into an output and returns it.
    fn custom(
        &mut self,
        lhs: Option<Self::Output>,
        token: Self::Input,
        rhs: Option<Self::Output>,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    /// Parses an iterator of [Self::Input] into an output and returns it. Returns [Err] if the
    /// input was empty or if an error occurs during parsing.
    ///
    /// See the examples and the README for more information.
    fn parse(&mut self, input: &mut I) -> Result<Self::Output, Self::Error> {
        let mut input = input.peekable();
        self.parse_precedence(&mut input, Precedence::MIN)
            .and_then(|opt| opt.ok_or_else(|| PrattError::EmptyInput.into()))
    }

    /// Parses an iterator of [Self::Input] while the current token's precedence is higher than
    /// `min_prec`, then returns the parsed output. Returns [None] if no matching input was given.
    ///
    /// This function should only be used internally by the parser itself.
    fn parse_precedence(
        &mut self,
        input: &mut Peekable<&mut I>,
        min_prec: Precedence,
    ) -> Result<Option<Self::Output>, Self::Error> {
        let mut lhs = None;

        loop {
            let affix = {
                let token = match input.peek() {
                    Some(token) => token,
                    None => return Ok(lhs),
                };
                let mode = match lhs {
                    Some(_) => ParseMode(__ParseMode::PostfixInfix),
                    None => ParseMode(__ParseMode::PrefixNilfix),
                };

                match self.query_affix(token, mode)? {
                    Some(a) if min_prec < a.left_precedence() => a,
                    _ => return Ok(lhs),
                }
            };

            let token = input.next().expect("unreachable");
            let rhs = self.parse_precedence(input, affix.right_precedence())?;
            lhs = Some(self.__dispatch(lhs, token, rhs, affix, input)?);
        }
    }

    /// Dispatches parsing of a token to the correct function. Returns [Err] if the token does not
    /// have the correct arguments.
    fn __dispatch(
        &mut self,
        lhs: Option<Self::Output>,
        token: Self::Input,
        rhs: Option<Self::Output>,
        affix: Affix,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error> {
        match affix {
            Affix::Nilfix => {
                match (lhs, rhs) {
                    (None, None) => (),
                    _ => return Err(PrattError::UnexpectedNilfix(token).into()),
                }
                self.nilfix(token, input)
            }
            Affix::Prefix(_) => {
                let rhs = match (lhs, rhs) {
                    (None, Some(rhs)) => rhs,
                    _ => return Err(PrattError::UnexpectedPrefix(token).into()),
                };
                self.prefix(token, rhs, input)
            }
            Affix::Postfix(_) => {
                let lhs = match (lhs, rhs) {
                    (Some(lhs), None) => lhs,
                    _ => return Err(PrattError::UnexpectedPostfix(token).into()),
                };
                self.postfix(lhs, token, input)
            }
            Affix::Infix(_, _) => {
                let (lhs, rhs) = match (lhs, rhs) {
                    (Some(lhs), Some(rhs)) => (lhs, rhs),
                    _ => return Err(PrattError::UnexpectedInfix(token).into()),
                };
                self.infix(lhs, token, rhs, input)
            }
            Affix::Custom(_, _) => self.custom(lhs, token, rhs, input),
        }
    }
}
