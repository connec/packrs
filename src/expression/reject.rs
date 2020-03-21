use crate::parser::Parser;
use crate::span::Span;

/// An expression that tries to match a sub-expression, producing no result and consuming no input.
pub struct Reject<P>(pub(crate) P);

impl<'a, P> Parser<'a> for Reject<P>
where
    P: Parser<'a>,
{
    type Value = ();
    type Error = ();

    /// Attempt to parse the sub-expression, and succeed if the sub-expression fails.
    ///
    /// If matching the sub-expression succeeds, a an empty failure is returned. If the
    /// sub-expression succeeds, and empty success is returned.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0
            .parse(input)
            .map_or_else(|_| Ok(Span::new(0..0, ())), |_| Err(Span::new(0..0, ())))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::Reject;

    #[test]
    fn p_match() {
        assert_eq!(
            Reject(TestExpr::ok(12..37)).parse("hello"),
            Err(Span::new(0..0, ()))
        );
    }

    #[test]
    fn p_error() {
        assert_eq!(
            Reject(TestExpr::err(12..37)).parse("hello"),
            Ok(Span::new(0..0, ()))
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String) {
        assert_eq!(
            Reject(&p).parse(&input),
            match p {
                ParseMatch(_, _) => Err(Span::new(0..0, ())),
                ParseError(_) => Ok(Span::new(0..0, ())),
            }
        );
    }
}
