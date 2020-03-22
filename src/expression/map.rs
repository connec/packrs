use crate::parser::Parser;
use crate::span::Span;

/// An expression that transforms a successful sub-expression result.
pub struct Map<P, F>(pub(crate) P, pub(crate) F);

impl<'i, P, F, U> Parser<'i> for Map<P, F>
where
    P: Parser<'i>,
    F: Fn(P::Value) -> U,
{
    type Value = U;
    type Error = P::Error;
    /// Attempt to parse the sub-expression, and map the result on success.
    ///
    /// If the sub-expression fails, the failure is returned verbatim.
    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0.parse(input).map(|value| value.map(&self.1))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;
    use std::cell::Cell;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::Map;

    #[test]
    fn p_match() {
        let called = Cell::new(false);
        let f = |_: TestValue| {
            called.set(true);
            42
        };

        assert_eq!(
            (Map(TestExpr::ok(23..89), f).parse("hello"), called.get()),
            (Ok(Span::new(23..89, 42)), true)
        );
    }

    #[test]
    fn p_error() {
        let called = Cell::new(false);
        let f = |_: TestValue| {
            called.set(true);
            42
        };

        assert_eq!(
            (Map(TestExpr::err(23..89), f).parse("hello"), called.get()),
            (Err(Span::new(23..89, TestError)), false)
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String, value: usize) {
        let called = Cell::new(false);
        let f = |_: TestValue| {
            called.set(true);
            value
        };

        assert_eq!(
            (Map(&p, f).parse(&input), called.get()),
            match p {
                ParseMatch(config, _) => (Ok(Span::new(config.range(), value)), true),
                ParseError(config) => (Err(Span::new(config.range(), TestError)), false),
            }
        );
    }
}
