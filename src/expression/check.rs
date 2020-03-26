//! An expression that evaluates a sub-expression, without consuming input.
//!
//! See [`check`].

use crate::parser::Parser;
use crate::span::Span;

/// Create a parser that will evaluate the given parser, without consuming any input.
///
/// If the given parser evaluates successfully, the result will be `Ok` with `()`. If the given
/// parser fails, the result will be an `Err` with the parse failure.
///
/// ```
/// use packrs::{ExpectedString, Parser, Span, check, string};
///
/// let check_hello = check(string("hello"));
///
/// assert_eq!(check_hello.parse("hello world"), Ok(Span::new(0..0, ())));
/// assert_eq!(check_hello.parse("world, hello"), Err(Span::new(0..1, ExpectedString("hello"))));
/// ```
pub fn check<'i, P>(parser: P) -> Check<P>
where
    P: Parser<'i>,
{
    Check(parser)
}

/// The struct returned from [`check`].
pub struct Check<P>(P);

impl<'i, P> Parser<'i> for Check<P>
where
    P: Parser<'i>,
{
    type Value = ();
    type Error = P::Error;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0.parse(input).map(|_| Span::new(0..0, ()))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::check;

    #[test]
    fn p_match() {
        assert_eq!(
            check(TestExpr::ok(12..37)).parse("hello"),
            Ok(Span::new(0..0, ()))
        );
    }

    #[test]
    fn p_error() {
        assert_eq!(
            check(TestExpr::err(12..37)).parse("hello"),
            Err(Span::new(12..37, TestError))
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String) {
        assert_eq!(
            check(&p).parse(&input),
            match p {
                ParseMatch(_, _) => Ok(Span::new(0..0, ())),
                ParseError(config) => Err(Span::new(config.range(), TestError)),
            }
        );
    }
}
