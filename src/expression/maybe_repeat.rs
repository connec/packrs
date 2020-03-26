//! An expression that evaluates a sub-expression repeatedly, until it fails.
//!
//! See [`maybe_repeat`].

use core::marker::PhantomData;

use crate::parser::{ParseResult, Parser};
use crate::span::Span;

/// Create a parser that will evaluate the given parser repeatedly, until it fails.
///
/// This will always return `Ok`, with a `Vec` of the parse results of all the successful
/// evaluations of the given parser. E.g., if the given parser fails the first evaluation, the
/// result will be `Ok(vec![])`.
///
/// ```
/// use packrs::{ParserExt, Span, chr, maybe_repeat};
///
/// let binary = maybe_repeat::<_, ()>(vec![chr('0'), chr('1')].one_of()).collect();
///
/// assert_eq!(binary.parse(""), Ok(Span::new(0..0, "".to_string())));
/// assert_eq!(binary.parse("0101"), Ok(Span::new(0..4, "0101".to_string())));
/// assert_eq!(binary.parse("012"), Ok(Span::new(0..2, "01".to_string())));
/// ```
pub fn maybe_repeat<'i, P, E>(parser: P) -> MaybeRepeat<P, E>
where
    P: Parser<'i>,
{
    MaybeRepeat(parser, PhantomData)
}

/// The struct returned from [`maybe_repeat`].
pub struct MaybeRepeat<P, E>(P, PhantomData<E>);

impl<'i, P, E> Parser<'i> for MaybeRepeat<P, E>
where
    P: Parser<'i>,
{
    type Value = Vec<Span<P::Value>>;
    type Error = E;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let mut end = 0;
        let mut values = Vec::new();

        while let Ok(value) = self.0.parse(&input[end..]).relative_to(end) {
            end = value.end();
            values.push(value);
        }

        Ok(Span::new(0..end, values))
    }
}

#[cfg(test)]
mod tests {
    use core::iter::repeat;
    use core::ops::Range;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::maybe_repeat;

    #[test]
    fn p_match() {
        assert_eq!(
            maybe_repeat::<_, ()>(TestExpr::ok_iters(0..1, 100))
                .parse(&repeat('a').take(100).collect::<String>()[..]),
            Ok(Span::new(
                0..100,
                repeat(TestValue)
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
            maybe_repeat::<_, ()>(TestExpr::err(77..367)).parse("whatever"),
            Ok(Span::new(0..0, vec![]))
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
            maybe_repeat::<_, ()>(&expr).parse(&input),
            match expr {
                ParseMatch(config, iters) => {
                    let segment = config.range().end;
                    let end = segment * iters as usize;
                    let values = (0..iters as usize)
                        .map(|i| Span::new(i * segment..(i + 1) * segment, TestValue))
                        .collect();
                    Ok(Span::new(0..end, values))
                }
                ParseError(_) => Ok(Span::new(0..0, vec![])),
            }
        );
    }
}
