use std::{fmt, iter::Peekable};

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
    Nilfix,
    Prefix(Precedence),
    Postfix(Precedence),
    Infix(Precedence, Associativity),
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

#[non_exhaustive]
#[derive(Debug)]
pub enum ParseMode {
    PrefixNilfix,
    PostfixInfix,
}

impl ParseMode {
    pub const fn nilfix(&self) -> bool {
        matches!(self, Self::PrefixNilfix)
    }

    pub const fn prefix(&self) -> bool {
        matches!(self, Self::PrefixNilfix)
    }

    pub const fn postfix(&self) -> bool {
        matches!(self, Self::PostfixInfix)
    }

    pub const fn infix(&self) -> bool {
        matches!(self, Self::PostfixInfix)
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
            Self::EmptyInput => f.write_str("empty input"),
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

    fn affix(&mut self, token: &Self::Input, mode: ParseMode)
        -> Result<Option<Affix>, Self::Error>;

    fn nilfix(
        &mut self,
        token: Self::Input,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    fn prefix(
        &mut self,
        op: Self::Input,
        rhs: Self::Output,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    fn postfix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    fn infix(
        &mut self,
        lhs: Self::Output,
        op: Self::Input,
        rhs: Self::Output,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    fn custom(
        &mut self,
        lhs: Option<Self::Output>,
        token: Self::Input,
        rhs: Option<Self::Output>,
        input: &mut Peekable<&mut I>,
    ) -> Result<Self::Output, Self::Error>;

    fn parse(&mut self, input: &mut I) -> Result<Self::Output, Self::Error> {
        let mut input = input.peekable();
        self.parse_precedence(&mut input, Precedence::MIN)
            .and_then(|opt| opt.ok_or_else(|| PrattError::EmptyInput.into()))
    }

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
                    Some(_) => ParseMode::PostfixInfix,
                    None => ParseMode::PrefixNilfix,
                };

                match self.affix(token, mode)? {
                    Some(a) if min_prec < a.left_precedence() => a,
                    _ => return Ok(lhs),
                }
            };

            let token = input.next().expect("unreachable");
            let rhs = self.parse_precedence(input, affix.right_precedence())?;
            lhs = Some(self.__dispatch(lhs, token, rhs, input, affix)?);
        }
    }

    fn __dispatch(
        &mut self,
        lhs: Option<Self::Output>,
        token: Self::Input,
        rhs: Option<Self::Output>,
        input: &mut Peekable<&mut I>,
        affix: Affix,
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
