use crate::parser::{ParseResult, Parser};
use crate::span::Span;

/// An expression for parsing a pair of sub-expressions whilst retaining their value types.
pub struct Join<P1, P2>(pub(crate) P1, pub(crate) P2);

impl<'i, P1, P2, E> Parser<'i> for Join<P1, P2>
where
    P1: Parser<'i, Error = E>,
    P2: Parser<'i, Error = E>,
{
    type Value = (Span<P1::Value>, Span<P2::Value>);
    type Error = E;

    /// Parse a pair of sub-expressions.
    ///
    /// Parsing succeeds if both sub-expressions succeed, and the result is a tuple of the
    /// sub-expression results. If any sub-expression fails, the failure is returned and any results
    /// up to that point are dropped.
    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let v1 = self.0.parse(input)?;
        let v2 = self.1.parse(&input[v1.end()..]).relative_to(v1.end())?;

        Ok(Span::new(v1.start()..v2.end(), (v1, v2)))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::Join;

    #[test]
    fn p1_match() {
        let p1 = TestExpr::ok(1..3);
        let p2 = TestExpr::err(0..2);
        let result = Join(&p1, &p2).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result),
            (1, 1, Err(Span::new(3..5, TestError)))
        );
    }

    #[test]
    fn p2_match() {
        let p1 = TestExpr::err(1..3);
        let p2 = TestExpr::ok(0..2);
        let result = Join(&p1, &p2).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result),
            (1, 0, Err(Span::new(1..3, TestError)))
        );
    }

    #[test]
    fn p1_p2_match() {
        let p1 = TestExpr::ok(1..3);
        let p2 = TestExpr::ok(0..2);
        let result = Join(&p1, &p2).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result),
            (
                1,
                1,
                Ok(Span::new(
                    1..5,
                    (Span::new(1..3, TestValue), Span::new(3..5, TestValue))
                ))
            )
        );
    }

    #[test]
    fn p1_p2_error() {
        let p1 = TestExpr::err(1..3);
        let p2 = TestExpr::err(0..2);
        let result = Join(&p1, &p2).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result),
            (1, 0, Err(Span::new(1..3, TestError)))
        );
    }

    #[derive(Clone, Debug)]
    struct TestData(TestExpr, TestExpr, String);

    impl Arbitrary for TestData {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let s1 = String::arbitrary(g);
            let s2 = String::arbitrary(g);
            let p = f64::arbitrary(g);
            let (e1, e2) = if p <= 0.25 {
                (TestExpr::ok(0..s1.len()), TestExpr::ok(0..s2.len()))
            } else if p <= 0.5 {
                (TestExpr::ok(0..s1.len()), TestExpr::err(0..s2.len()))
            } else if p <= 0.75 {
                (TestExpr::err(0..s1.len()), TestExpr::ok(0..s2.len()))
            } else {
                (TestExpr::err(0..s1.len()), TestExpr::err(0..s2.len()))
            };

            TestData(e1, e2, s1 + &s2)
        }
    }

    #[quickcheck]
    fn parse(TestData(p1, p2, input): TestData) {
        let result = Join(&p1, &p2).parse(&input);
        match (&p1, &p2) {
            (ParseMatch(config1, _), ParseMatch(config2, _)) => {
                assert_eq!(
                    result,
                    Ok(Span::new(
                        config1.range().start..config1.range().end + config2.range().end,
                        (
                            Span::new(config1.range(), TestValue),
                            Span::new(config2.range(), TestValue).relative_to(config1.range().end)
                        )
                    ))
                );
            }
            (ParseMatch(config1, _), ParseError(config2)) => {
                assert_eq!(
                    result,
                    Err(Span::new(config2.range(), TestError).relative_to(config1.range().end))
                );
            }
            (ParseError(config), _) => {
                assert_eq!(result, Err(Span::new(config.range(), TestError)));
            }
        }
    }
}
