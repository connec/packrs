//! An expression that evaluates a sub-expression and rejects successful results.
//!
//! See [`crate::Parser::reject`].

use crate::parser::Parser;
use crate::span::Span;

/// The struct returned from [`crate::Parser::reject`].
pub struct Reject<P>(pub(crate) P);

impl<P> Parser for Reject<P>
where
    P: Parser,
{
    type Value = ();
    type Error = ();

    fn parse(&self, input: &'_ str) -> Result<Span<Self::Value>, Span<Self::Error>> {
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
