use crate::parser::Parser;
use crate::span::Span;

/// An expression that tries to match a sub-expression, producing no result and consuming no input.
pub struct Check<P>(pub(crate) P);

impl<'i, P> Parser<'i> for Check<P>
where
    P: Parser<'i>,
{
    type Value = ();
    type Error = P::Error;
    /// Attempt to parse the sub-expression, and return an empty value on success.
    ///
    /// If matching the sub-expression fails, the failure is returned verbatim. If the
    /// sub-expression succeeds, the value is discarded and an empty `Span` is returned.
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

    use super::Check;

    #[test]
    fn p_match() {
        assert_eq!(
            Check(TestExpr::ok(12..37)).parse("hello"),
            Ok(Span::new(0..0, ()))
        );
    }

    #[test]
    fn p_error() {
        assert_eq!(
            Check(TestExpr::err(12..37)).parse("hello"),
            Err(Span::new(12..37, TestError))
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String) {
        assert_eq!(
            Check(&p).parse(&input),
            match p {
                ParseMatch(_, _) => Ok(Span::new(0..0, ())),
                ParseError(config) => Err(Span::new(config.range(), TestError)),
            }
        );
    }
}
