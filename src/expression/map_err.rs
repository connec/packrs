use crate::parser::Parser;
use crate::span::Span;

/// An expression that transforms a failed sub-expression result.
pub struct MapErr<P, F>(P, F);

impl<'a, P, F, E, U> Parser<'a> for MapErr<P, F>
where
    P: Parser<'a, Error = E>,
    F: Fn(E) -> U,
{
    type Value = P::Value;
    type Error = U;
    /// Attempt to parse the sub-expression, and map the result on failure.
    ///
    /// If the sub-expression succeeds, the result is returned verbatim.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0.parse(input).map_err(|value| value.map(&self.1))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;
    use std::cell::Cell;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::MapErr;

    #[test]
    fn p_match() {
        let called = Cell::new(false);
        let f = |_: TestError| {
            called.set(true);
            42
        };

        assert_eq!(
            (MapErr(TestExpr::ok(23..89), f).parse("hello"), called.get()),
            (Ok(Span::new(23..89, TestValue)), false)
        );
    }

    #[test]
    fn p_error() {
        let called = Cell::new(false);
        let f = |_: TestError| {
            called.set(true);
            42
        };

        assert_eq!(
            (
                MapErr(TestExpr::err(23..89), f).parse("hello"),
                called.get()
            ),
            (Err(Span::new(23..89, 42)), true)
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String, value: usize) {
        let called = Cell::new(false);
        let f = |_: TestError| {
            called.set(true);
            value
        };

        assert_eq!(
            (MapErr(&p, f).parse(&input), called.get()),
            match p {
                ParseMatch(config, _) => (Ok(Span::new(config.range(), TestValue)), false),
                ParseError(config) => (Err(Span::new(config.range(), value)), true),
            }
        );
    }
}
