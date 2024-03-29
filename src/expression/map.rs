//! An expression that evaluates a sub-expression, and transforms successful results.
//!
//! See [`crate::Parser::map`].

use crate::parser::Parser;
use crate::span::Span;

/// The struct returned from [`crate::Parser::map`].
pub struct Map<P, F>(pub(crate) P, pub(crate) F);

impl<P, F, U> Parser for Map<P, F>
where
    P: Parser,
    F: Fn(P::Value) -> U,
{
    type Value = U;
    type Error = P::Error;

    fn parse(&self, input: &'_ str) -> Result<Span<Self::Value>, Span<Self::Error>> {
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
