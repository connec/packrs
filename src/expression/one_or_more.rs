use crate::parser::{ParseResult, Parser};
use crate::span::Span;

/// An expression that matches a sub-expression at least once, then as many times as it can.
pub struct OneOrMore<P>(P);

impl<'a, P> Parser<'a> for OneOrMore<P>
where
    P: Parser<'a>,
{
    type Value = Vec<Span<P::Value>>;
    type Error = P::Error;
    /// Repeatedly parse the sub-expression until it fails, returning an array of the sucessful
    /// results.
    ///
    /// This fails if the first attempt to match the sub-expression fails, returning the failure.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
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
    use core::iter::repeat;
    use core::ops::Range;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::OneOrMore;

    #[test]
    fn p_match() {
        assert_eq!(
            OneOrMore(TestExpr::ok_iters(0..1, 100))
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
            OneOrMore(TestExpr::err(77..367)).parse("whatever"),
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
            OneOrMore(&expr).parse(&input),
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
