//! An expression that evaluates sub-expressions in order.
//!
//! See [`all_of`].

use crate::parser::{ParseResult, Parser};
use crate::span::Span;

/// Create a parser that will evaluate the given parsers in order against an input.
///
/// If all of the given parsers can be evaluated successfully, the result will be `Ok` with a `Vec`
/// of the successfully parsed values. If any parser fails, the result will be an `Err` with the
/// parse failure.
///
/// Note that all parsers must have the same type. [`map`](super::map::map) and
/// [`map_err`](super::map_err::map_err) can be used to unify value and errors types, and
/// [`Parser::as_ref`](crate::Parser::as_ref) or [`Parser::boxed`](crate::Parser::boxed) can be used
/// to unify different parser types.
///
/// ```
/// use packrs::{ExpectedChar, Parser, ParserExt, Span, all_of, chr};
///
/// let hello = all_of("hello".chars().map(chr).collect()).collect();
///
/// assert_eq!(hello.parse("hello world"), Ok(Span::new(0..5, "hello".to_string())));
/// assert_eq!(hello.parse("world"), Err(Span::new(0..1, ExpectedChar('h'))));
/// ```
pub fn all_of<'i, P>(parsers: Vec<P>) -> AllOf<P>
where
    P: Parser<'i>,
{
    AllOf(parsers)
}

/// The struct returned from [`all_of`].
pub struct AllOf<P>(Vec<P>);

impl<'i, P> Parser<'i> for AllOf<P>
where
    P: Parser<'i>,
{
    type Value = Vec<Span<P::Value>>;
    type Error = P::Error;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
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

    use super::all_of;

    #[test]
    fn empty() {
        assert_eq!(
            all_of::<TestExpr>(vec![]).parse("hello"),
            Ok(Span::new(0..0, vec![]))
        );
    }

    #[test]
    fn p1_match() {
        let p1 = TestExpr::ok(1..3);
        let p2 = TestExpr::err(0..2);
        let result = all_of(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result,),
            (1, 1, Err(Span::new(3..5, TestError)))
        );
    }

    #[test]
    fn p2_match() {
        let p1 = TestExpr::err(1..3);
        let p2 = TestExpr::ok(0..2);
        let result = all_of(vec![&p1, &p2]).parse("hello");
        assert_eq!(
            (p1.config().calls(), p2.config().calls(), result,),
            (1, 0, Err(Span::new(1..3, TestError)))
        );
    }

    #[test]
    fn p1_p2_match() {
        let p1 = TestExpr::ok(1..3);
        let p2 = TestExpr::ok(0..2);
        let result = all_of(vec![&p1, &p2]).parse("hello");
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
        let result = all_of(vec![&p1, &p2]).parse("hello");
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
                            if u8::arbitrary(g) > 4 {
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
        let result = all_of(ps.iter().collect()).parse(&input);
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
