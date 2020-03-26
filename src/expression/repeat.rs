//! An expression that evaluates a sub-expression at least once, then repeatedly until it fails.
//!
//! See [`repeat`].

use crate::parser::{ParseResult, Parser};
use crate::span::Span;

/// Create a parser that will evaluate the given parser repeatedly, until it fails.
///
/// Unlike [`maybe_repeat`](super::maybe_repeat::maybe_repeat) this will fail if the given parser
/// fails to match the first time it is evaluated, returning an `Err` with the parse failure. If the
/// first evaluation succeeds, the result will be `Ok` with a `Vec` of the parse results of
/// successful evaluations.
///
/// ```
/// use packrs::{Parser, ParserExt, Span, UnexpectedEndOfInput, any, chr, repeat};
///
/// let first_word = repeat(
///     vec![
///         chr(' ').reject().map(|_| "").map_err(|_| UnexpectedEndOfInput).boxed(),
///         any().boxed(),
///     ]
///     .all_of()
///     .map(|mut v| v.pop().unwrap().take())
/// ).collect();
///
/// assert_eq!(first_word.parse("hello world"), Ok(Span::new(0..5, "hello".to_string())));
/// assert_eq!(first_word.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
/// ```
pub fn repeat<'i, P>(parser: P) -> Repeat<P>
where
    P: Parser<'i>,
{
    Repeat(parser)
}

/// The struct returned from [`repeat`].
pub struct Repeat<P>(P);

impl<'i, P> Parser<'i> for Repeat<P>
where
    P: Parser<'i>,
{
    type Value = Vec<Span<P::Value>>;
    type Error = P::Error;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let value = self.0.parse(input)?;
        let mut end = value.end();
        let mut values = vec![value];

        while let Ok(value) = self.0.parse(&input[end..]).relative_to(end) {
            end = value.end();
            values.push(value);
        }

        Ok(Span::new(0..end, values))
    }
}

#[cfg(test)]
mod tests {
    use core::iter::repeat as iter_repeat;
    use core::ops::Range;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::repeat;

    #[test]
    fn p_match() {
        assert_eq!(
            repeat(TestExpr::ok_iters(0..1, 100))
                .parse(&iter_repeat('a').take(100).collect::<String>()[..]),
            Ok(Span::new(
                0..100,
                iter_repeat(TestValue)
                    .take(100)
                    .enumerate()
                    .map(|(i, v)| Span::new(i..=i, v))
                    .collect()
            ))
        );
    }

    #[test]
    fn p_error() {
        assert_eq!(
            repeat(TestExpr::err(77..367)).parse("whatever"),
            Err(Span::new(77..367, TestError))
        );
    }

    #[derive(Clone, Debug)]
    struct TestData((TestExpr, String));

    impl Arbitrary for TestData {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let iters = u8::arbitrary(g);
            let input = String::arbitrary(g);
            TestData(if iters == 0 {
                (TestExpr::err(Range::arbitrary(g)), input)
            } else {
                (
                    TestExpr::ok_iters(0..input.len(), iters),
                    input.repeat(iters as usize + 1),
                )
            })
        }
    }

    #[quickcheck]
    fn parse(TestData((expr, input)): TestData) {
        assert_eq!(
            repeat(&expr).parse(&input),
            match expr {
                ParseMatch(config, iters) => {
                    let segment = config.range().end;
                    let end = segment * iters as usize;
                    let values = (0..iters as usize)
                        .map(|i| Span::new(i * segment..(i + 1) * segment, TestValue))
                        .collect();
                    Ok(Span::new(0..end, values))
                }
                ParseError(config) => Err(Span::new(config.range(), TestError)),
            }
        );
    }
}
