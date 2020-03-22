use core::cmp::{max, min};

use crate::parser::Parser;
use crate::span::Span;

/// An expression that returns the first successful match from a sequence of sub-expressions.
pub struct OneOf<P>(pub(crate) Vec<P>);

impl<'i, P> Parser<'i> for OneOf<P>
where
    P: Parser<'i>,
{
    type Value = P::Value;
    type Error = Vec<Span<P::Error>>;

    /// Parse a sequence of sub-expressions, returning the result of the first one that succeeds.
    ///
    /// Parsing succeeds if any sub-expression succeeds, and the result is the result of the
    /// successful sub-expression (any preceeding failures are dropped). If all sub-expressions
    /// fail, all the failures are returned.
    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let mut start = usize::max_value();
        let mut end = 0;
        let mut errors = Vec::new();

        for expr in self.0.iter() {
            let error = match expr.parse(input) {
                Ok(value) => return Ok(value),
                Err(error) => error,
            };
            start = min(start, error.start());
            end = max(end, error.end());
            errors.push(error);
        }

        if start == usize::max_value() {
            start = 0;
        }
        Err(Span::new(start..end, errors))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::OneOf;

    #[test]
    fn empty() {
        assert_eq!(
            OneOf::<TestExpr>(vec![]).parse("hello"),
            Err(Span::new(0..0, vec![]))
        );
    }

    #[test]
    fn p1_match() {
        let p1 = TestExpr::ok(32..71);
        let p2 = TestExpr::err(12..29);
        let result = OneOf(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result),
            (1, 0, Ok(Span::new(32..71, TestValue)))
        );
    }

    #[test]
    fn p2_match() {
        let p1 = TestExpr::err(32..71);
        let p2 = TestExpr::ok(12..29);
        let result = OneOf(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result),
            (1, 1, Ok(Span::new(12..29, TestValue)))
        );
    }

    #[test]
    fn p1_and_p2_match() {
        let p1 = TestExpr::ok(32..71);
        let p2 = TestExpr::ok(12..29);
        let result = OneOf(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result),
            (1, 0, Ok(Span::new(32..71, TestValue)))
        );
    }

    #[test]
    fn p1_and_p2_error() {
        let p1 = TestExpr::err(32..71);
        let p2 = TestExpr::err(12..29);
        let result = OneOf(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result,),
            (
                1,
                1,
                Err(Span::new(
                    12..71,
                    vec![Span::new(32..71, TestError), Span::new(12..29, TestError)]
                )),
            )
        );
    }

    #[quickcheck]
    fn parse(ps: Vec<TestExpr>, input: String) {
        let first_match = ps.iter().enumerate().find_map(|(i, p)| {
            if p.is_ok() {
                Some((i, p.clone()))
            } else {
                None
            }
        });
        let result = OneOf(ps.iter().collect()).parse(&input);
        match first_match {
            Some((i, p)) => {
                assert_eq!(result, Ok(Span::new(p.config().range(), TestValue)));
                assert!(ps.iter().take(i + 1).all(|p| p.config().calls() == 1));
                assert!(ps.iter().skip(i + 1).all(|p| p.config().calls() == 0));
            }
            None if !ps.is_empty() => {
                let start = ps.iter().map(|p| p.config().range().start).min().unwrap();
                let end = ps.iter().map(|p| p.config().range().end).max().unwrap();
                let errors = ps
                    .iter()
                    .map(|p| Span::new(p.config().range(), TestError))
                    .collect();
                assert_eq!(result, Err(Span::new(start..end, errors)));
                assert!(ps.iter().all(|p| p.config().calls() == 1));
            }
            None => {
                assert_eq!(result, Err(Span::new(0..0, vec![])));
            }
        }
    }
}
