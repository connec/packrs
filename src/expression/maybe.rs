use core::convert::Infallible;

use crate::parser::Parser;
use crate::span::Span;

/// An expression that tries to match a sub-expression, and succeeds regardless.
pub struct Maybe<P>(P);

impl<'a, P> Parser<'a> for Maybe<P>
where
    P: Parser<'a>,
{
    type Value = Option<Span<P::Value>>;
    type Error = Infallible;
    /// Attempt to parse the sub-expression and succeed with an `Option`, depending on the result.
    ///
    /// This always succeeds, returning `Some` containing the successful result or `None` if the
    /// sub-expression fails.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        Ok(match self.0.parse(input) {
            Ok(value) => Span::new(value.start()..value.end(), Some(value)),
            Err(_) => Span::new(0..0, None),
        })
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::Maybe;

    #[test]
    fn p_match() {
        assert_eq!(
            Maybe(TestExpr::ok(83..98)).parse("hello"),
            Ok(Span::new(83..98, Some(Span::new(83..98, TestValue))))
        );
    }

    #[test]
    fn p_error() {
        assert_eq!(
            Maybe(TestExpr::err(5..458)).parse("hello"),
            Ok(Span::new(0..0, None))
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String) {
        assert_eq!(
            Maybe(&p).parse(&input),
            Ok(match p {
                ParseMatch(config, _) =>
                    Span::new(config.range(), Some(Span::new(config.range(), TestValue))),
                ParseError(_) => Span::new(0..0, None),
            })
        );
    }
}
