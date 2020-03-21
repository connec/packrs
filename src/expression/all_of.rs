use crate::parser::{ParseResult, Parser};
use crate::span::Span;

/// An expression for parsing a sequence of sub-expressions.
pub struct AllOf<P>(pub(crate) Vec<P>);

impl<'a, P> Parser<'a> for AllOf<P>
where
    P: Parser<'a>,
{
    type Value = Vec<Span<P::Value>>;
    type Error = P::Error;

    /// Parse a sequence of sub-expressions.
    ///
    /// Parsing succeeds if all sub-expressions succeed, and the result is a `Vec` of the
    /// sub-expression results. If any sub-expression fails, the failure is returned and any results
    /// up to that point are dropped.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let mut start = 0;
        let mut end = 0;
        let mut values = Vec::with_capacity(self.0.len());
        let mut iter = self.0.iter();

        if let Some(expr) = iter.next() {
            let value = expr.parse(input)?;
            start = value.start();
            end = value.end();
            values.push(value);
        }

        for expr in iter {
            let value = expr.parse(&input[end..]).relative_to(end)?;
            end = value.end();
            values.push(value);
        }

        Ok(Span::new(start..end, values))
    }
}

#[cfg(test)]
mod tests {
    use core::cmp::min;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::AllOf;

    #[test]
    fn empty() {
        assert_eq!(
            AllOf::<TestExpr>(vec![]).parse("hello"),
            Ok(Span::new(0..0, vec![]))
        );
    }

    #[test]
    fn p1_match() {
        let p1 = TestExpr::ok(1..3);
        let p2 = TestExpr::err(0..2);
        let result = AllOf(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result,),
            (1, 1, Err(Span::new(3..5, TestError)))
        );
    }

    #[test]
    fn p2_match() {
        let p1 = TestExpr::err(1..3);
        let p2 = TestExpr::ok(0..2);
        let result = AllOf(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result,),
            (1, 0, Err(Span::new(1..3, TestError)))
        );
    }

    #[test]
    fn p1_p2_match() {
        let p1 = TestExpr::ok(1..3);
        let p2 = TestExpr::ok(0..2);
        let result = AllOf(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result,),
            (
                1,
                1,
                Ok(Span::new(
                    1..5,
                    vec![Span::new(1..3, TestValue), Span::new(3..5, TestValue)]
                ))
            )
        );
    }

    #[test]
    fn p1_p2_error() {
        let p1 = TestExpr::err(1..3);
        let p2 = TestExpr::err(0..2);
        let result = AllOf(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result,),
            (1, 0, Err(Span::new(1..3, TestError)))
        );
    }

    #[derive(Clone, Debug)]
    struct TestData((Vec<TestExpr>, String));

    impl Arbitrary for TestData {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            TestData(
                (0..usize::arbitrary(g))
                    .map(|_| {
                        let s = String::arbitrary(g);
                        (
                            if f64::arbitrary(g) > 0.1 {
                                TestExpr::ok(0..s.len())
                            } else {
                                TestExpr::err(0..s.len())
                            },
                            s,
                        )
                    })
                    .unzip(),
            )
        }
    }

    #[quickcheck]
    fn parse(TestData((ps, input)): TestData) {
        let ps = ps
            .into_iter()
            .map(|p| match p {
                ParseMatch(config, _) => TestExpr::ok(
                    min(config.range().start, input.len())..min(config.range().end, input.len()),
                ),
                ParseError(config) => TestExpr::err(
                    min(config.range().start, input.len())..min(config.range().end, input.len()),
                ),
            })
            .collect::<Vec<_>>();
        let first_error = ps.iter().enumerate().find_map(|(i, p)| {
            if p.is_ok() {
                None
            } else {
                Some((i, p.clone()))
            }
        });
        let result = AllOf(ps.iter().collect()).parse(&input);
        match first_error {
            Some((i, p)) => {
                let end = ps.iter().take(i).map(|p| p.config().range().end).sum();
                assert_eq!(
                    result,
                    Err(Span::new(p.config().range(), TestError).relative_to(end))
                );
                assert!(ps.iter().take(i + 1).all(|p| p.config().calls() == 1));
                assert!(ps.iter().skip(i + 1).all(|p| p.config().calls() == 0));
            }
            None => {
                let start = ps.get(0).map_or(0, |p| p.config().range().start);
                let end = ps.iter().map(|p| p.config().range().end).sum();
                let values = ps
                    .iter()
                    .enumerate()
                    .map(|(i, p)| {
                        let end = ps.iter().take(i).map(|p| p.config().range().end).sum();
                        Span::new(p.config().range(), TestValue).relative_to(end)
                    })
                    .collect();
                assert_eq!(result, Ok(Span::new(start..end, values)));
                assert!(ps.iter().all(|p| p.config().calls() == 1));
            }
        }
    }
}
